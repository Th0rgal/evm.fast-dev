import InitECandidate.Solver.Wave8Stage.WordToStackBounded
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.Assembly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
Zero-extra-clock WordToStack leaves. Each proof is adapted from the pinned
Flapjack constructor and retains the same guards and complete result relation.
The actual witness zero is exposed with its bound, including leaf timeouts,
allocation failure, and FFI termination. Helpers with private upstream names
are reproduced locally when needed by the adapted proof.
-/

namespace InitECandidate.Solver.Wave8Stage.WordToStackZeroClock
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open InitECandidate.Solver.Wave8Stage.WordToStackBounded


namespace Control

theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate .skip source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.skip : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions (.skip : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false .skip (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.skip : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, Nat.le_refl 0, target, none, ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_skip]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

theorem compCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.break label) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.break label) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.break label) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.break label) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.break label) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, Nat.le_refl 0, target, some (.break label), ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_break]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

theorem compCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (label : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.continue label) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.continue label) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.continue label) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.continue label) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.continue label) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have execution := premises.1
  simp only [WordSemStateFiniteExact.evaluate] at execution
  obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
  have compilation := premises.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative] at programEq
  subst compiled
  subst result
  subst sourcePost
  refine ⟨0, Nat.le_refl 0, target, some (.continue label), ?_, ?_⟩
  · simp only [Nat.add_zero, StackSemEvaluate.evaluate_continue]
  · simpa only [compCorrectResult, compileResult, Option.map_some, Option.map_none,
      ne_eq, not_true_eq_false, ↓reduceIte] using premises.2.2.1

end Control

namespace Alloc

open Flapjack.WordToStackProofs.CompCorrect.Alloc

theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dest : Nat) (names : WordLangCutsetsHOL) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.alloc dest names) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.alloc dest names) : WordLangProgHOL (BitVec width)) = true ∧
      flatExpConventions ((.alloc dest names) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.alloc dest names) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.alloc dest names) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨execution, notError, related, conventions, -, compilation, hbsn, hbsl, hpre, -,
    maxVar⟩ := premises
  obtain ⟨rfl, hc1, hc2⟩ := allocConventions k dest names conventions
  have hn1 : ∀ x, sptDomain names.1 x → x % 2 = 0 ∧ k ≤ x / 2 :=
    fun x hx => ⟨(hc1 x hx).1, by have := (hc1 x hx).2; omega⟩
  have hn2 : ∀ x, sptDomain names.2 x → x % 2 = 0 ∧ k ≤ x / 2 :=
    fun x hx => ⟨(hc2 x hx).1, by have := (hc2 x hx).2; omega⟩
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, -, -, -, -, -, r7, -, -, r10, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, -, r35, -, -, -, -⟩ := related'
  -- the allocation request comes from source variable 2, i.e. target register 1
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hg : WordSemStateFiniteExact.getVar 2 source with _ | (w | ⟨_, _⟩)
  · simp only [hg, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  rotate_left
  · simp only [hg, Prod.mk.injEq] at execution; exact absurd execution.1.symm notError
  simp only [hg] at execution
  have hg1 : StackSemStateOps.getVar 1 target = some (.word w) :=
    StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 2 _
      ⟨related, hg, rfl, by omega⟩
  rcases hcut : wordSemCutEnvs names source.locals with _ | envs
  · simp only [WordSemStateFiniteExact.alloc, hcut, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [compNative] at compilation
  rcases hwl : wLiveNative names (bs, n) (k, f, frame) with ⟨q1, bsw⟩
  rw [hwl] at compilation
  simp only [Prod.mk.injEq] at compilation
  obtain ⟨rfl, rfl⟩ := compilation
  have htarget : {target with clock := target.clock + 0} = target := by simp
  -- the result relation for a simulated allocation
  have finish : ∀ (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
      (result = none → res1 = none ∧ stateRel ac k f frame sourcePost t1 lens 0) →
      (result ≠ none → result = some .notEnoughSpace ∧ res1 = some (.halt (.word 1)) ∧
          sourcePost.clock = t1.clock ∧ sourcePost.ffi = t1.ffi) →
      compCorrectResult ac k f frame source sourcePost t1 result res1 lens := by
    intro t1 res1 hnone hsome
    unfold compCorrectResult
    by_cases hres : result = none
    · obtain ⟨rfl, hrel1⟩ := hnone hres
      subst hres
      simp only [Option.map_none, ne_eq, not_true_eq_false, if_false]
      exact hrel1
    · obtain ⟨rfl, rfl, hcl, hff⟩ := hsome hres
      simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
      exact ⟨hff, hcl⟩
  by_cases hf : 1 ≤ f
  · obtain ⟨t5, hev5, hpush5, hrel5, -, -, hget5⟩ :=
      EvaluateWLive.evaluateWLive ac k f frame names bs n q1 bsPost nPost source target lens envs
        ⟨by rw [hwl], hn1, hn2, related, hf, hcut, hbsn, hbsl, hpre⟩
    have hrel5' := hrel5
    unfold stateRel at hrel5'
    have hclock5 : t5.clock = target.clock := hrel5'.1.symm.trans r1
    have huse5 : t5.useAlloc = true := hrel5'.2.2.2.2.2.2.1
    have hg5 : StackSemStateOps.getVar 1 t5 = some (.word w) :=
      (hget5 1 (by omega)).trans hg1
    obtain ⟨t1, res1, halloc1, hif⟩ :=
      AllocStateRel.allocImpAlloc ac k f frame w names source sourcePost result t5 lens envs
        ⟨execution, hn1, hn2, hf, hrel5, hpush5, hcut, notError⟩
    refine ⟨0, Nat.le_refl 0, t1, res1, ?_, finish t1 res1
      (fun hr => by rw [if_pos hr] at hif; exact ⟨hif.1, hif.2.1⟩)
      (fun hr => by rw [if_neg hr] at hif; exact hif)⟩
    rw [htarget, StackSemEvaluate.evaluate_seq, hev5]
    simp only [StackSemControl.fixClock]
    rw [show min target.clock t5.clock = t5.clock by omega]
    show StackSemEvaluate.evaluate (Prog.alloc 1, t5) = (res1, t1)
    rw [StackSemEvaluate.evaluate_alloc]
    simp only [huse5, Bool.not_true, Bool.false_eq_true, if_false, hg5]
    exact halloc1
  · have hf0 : f = 0 := by omega
    have hfr0 : frame = 0 := by
      by_cases h : frame = 0
      · exact h
      · rw [if_neg h] at r35; omega
    subst hf0 hfr0
    simp only [wLiveNative, if_true, Prod.mk.injEq] at hwl
    obtain ⟨rfl, -⟩ := hwl
    -- with no frame, the stack-placed cutset names cannot exist
    have hempty : ∀ t : Spt Unit, (∀ x, sptDomain t x → 2 * k ≤ x) →
        maxList ((sptToAList t).map Prod.fst) < 2 * k → sptDomain t = fun _ => False := by
      intro t hge hlt
      funext x
      apply propext
      constructor
      · intro hx
        obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp hx
        have hm := maxList_ge_of_mem ((sptToAList t).map Prod.fst) x
          (List.mem_map.mpr ⟨(x, u), (sptToAList_mem_iff_lookup t x u).mpr hu, rfl⟩)
        have := hge x hx
        omega
      · exact False.elim
    simp only [maxVarHOL, cutsetsMaxHOL, max_lt_iff] at maxVar
    have hd1 := hempty names.1 (fun x hx => (hc1 x hx).2) (by omega)
    have hd2 := hempty names.2 (fun x hx => (hc2 x hx).2) (by omega)
    obtain ⟨t1, res1, halloc1, hif⟩ :=
      AllocStateRel.allocImpAlloc2 ac k w names source sourcePost result target lens
        ⟨execution, related, hd1, hd2, notError⟩
    refine ⟨0, Nat.le_refl 0, t1, res1, ?_, finish t1 res1
      (fun hr => by rw [if_pos hr] at hif; exact ⟨hif.1, hif.2.1⟩)
      (fun hr => by rw [if_neg hr] at hif; exact hif)⟩
    rw [htarget, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_skip]
    simp only [StackSemControl.fixClock, Nat.min_self]
    show StackSemEvaluate.evaluate (Prog.alloc 1, target) = (res1, t1)
    rw [StackSemEvaluate.evaluate_alloc]
    simp only [r7, Bool.not_true, Bool.false_eq_true, if_false, hg1]
    exact halloc1

end Alloc

namespace StoreConsts

open Flapjack.WordToStackProofs.CompCorrect.StoreConsts

private theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (first second addressRegister offsetRegister : Nat)
    (words : List (Bool × BitVec width))
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate
      (.storeConsts first second addressRegister offsetRegister words) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ address offset : BitVec width,
      WordSemStateFiniteExact.getVar addressRegister source = some (.word address) ∧
      WordSemStateFiniteExact.getVar offsetRegister source = some (.word offset) ∧
      wordSemConstAddresses address words source.mdomain = true ∧
      result = none ∧
      post = WordSemStateFiniteExact.setVar addressRegister
        (.word (address + wordSemBytesInWord * BitVec.ofNat width words.length))
        (WordSemStateFiniteExact.setVar offsetRegister (.word offset)
          (WordSemStateFiniteExact.unsetVar first (WordSemStateFiniteExact.unsetVar second
            {source with memory := wordSemConstWrites address offset words source.memory}))) := by
  cases addressRead : WordSemStateFiniteExact.getVar addressRegister source with
  | none =>
    simp [WordSemStateFiniteExact.evaluate,addressRead] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  | some addressValue =>
    cases addressValue with
    | loc l n =>
      simp [WordSemStateFiniteExact.evaluate,addressRead] at execution
      obtain ⟨rfl,rfl⟩ := execution
      contradiction
    | word address =>
      cases offsetRead : WordSemStateFiniteExact.getVar offsetRegister source with
      | none =>
        simp [WordSemStateFiniteExact.evaluate,addressRead,offsetRead] at execution
        obtain ⟨rfl,rfl⟩ := execution
        contradiction
      | some offsetValue =>
        cases offsetValue with
        | loc l n =>
          simp [WordSemStateFiniteExact.evaluate,addressRead,offsetRead] at execution
          obtain ⟨rfl,rfl⟩ := execution
          contradiction
        | word offset =>
          by_cases addresses : wordSemConstAddresses address words source.mdomain = true
          · simp only [WordSemStateFiniteExact.evaluate,addressRead,offsetRead,addresses,
              not_true_eq_false,↓reduceIte,Prod.mk.injEq] at execution
            obtain ⟨rfl,rfl⟩ := execution
            exact ⟨address,offset,rfl,rfl,addresses,rfl,rfl⟩
          · simp [WordSemStateFiniteExact.evaluate,addressRead,offsetRead,addresses] at execution
            obtain ⟨rfl,rfl⟩ := execution
            contradiction

/-- Flapjack infrastructure naming the complete actual source update; HOL
writes this state inline in the constructor's evaluator equation. -/
private def sourcePost {width : Nat} [NeZero width] {C F : Type}
    (address offset : BitVec width) (words : List (Bool × BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :=
  WordSemStateFiniteExact.setVar 4
    (.word (address + wordSemBytesInWord * BitVec.ofNat width words.length))
    (WordSemStateFiniteExact.setVar 6 (.word offset)
      (WordSemStateFiniteExact.unsetVar 0 (WordSemStateFiniteExact.unsetVar 2
        {source with memory := wordSemConstWrites address offset words source.memory})))

/-- Flapjack infrastructure naming the actual target writes, including its
bitmap-index prelude and allocation-mode register removal. -/
private def targetPost {width : Nat} [NeZero width] {C F : Type}
    (k index : Nat) (address offset : BitVec width) (words : List (Bool × BitVec width))
    (target : StackSemStateFiniteExact width C F) :=
  StackSemStoreConsts.unsetVarZero
    (StackSemStateOps.setVar k (.word 1) (StackSemStateOps.setVar (k+1) (.word 1)
      (StackSemStateOps.setVar 1 (.word 1) (StackSemStateOps.setVar 2
        (.word (address + wordSemBytesInWord * BitVec.ofNat width words.length))
        {StackSemStateOps.setVar 1 (.word (BitVec.ofNat width index)) target with
          memory := wordSemConstWrites address offset words target.memory}))))

/-- Flapjack infrastructure for the original inline StoreConsts postrelation:
all original stateRel conjuncts, not merely memory or register observations. -/
private theorem postRelated {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width) (k f frame index : Nat)
    (address offset : BitVec width) (words : List (Bool × BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (related : stateRel ac k f frame source target lens 0)
    (offsetRead : WordSemStateFiniteExact.getVar 6 source = some (.word offset)) :
    stateRel ac k f frame (sourcePost address offset words source)
      (targetPost k index address offset words target) lens 0 := by
  unfold stateRel at related ⊢
  obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
    h37,h38,hloc⟩ := related
  refine ⟨h1,h2,h3,h4,h5,h6,h7,?_,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
    h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,?_,
    h37,h38,?_⟩
  · exact congrArg (wordSemConstWrites address offset words) h8
  · exact sptWfInsert 4 _ _ (sptWfInsert 6 _ _
      (sptWfDelete _ 0 (sptWfDelete _ 2 h36)))
  · intro n value found
    change sptLookup n (sptInsert 4 _ (sptInsert 6 _
      (sptDelete 0 (sptDelete 2 source.locals)))) = some value at found
    have offsetPlacement := (hloc 6 (.word offset) offsetRead).2
    have offsetPhysical : 6 / 2 < k := by omega
    rw [if_pos offsetPhysical] at offsetPlacement
    by_cases isAddress : n = 4
    · subst n
      rw [sptLookup_sptInsert_same] at found
      have eq := Option.some.inj found
      subst value
      simp [targetPost, StackSemStoreConsts.unsetVarZero, StackSemStateOps.setVar,
        HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL,
        show 2 < k by omega, show 2 ≠ k by omega, show 2 ≠ k+1 by omega]
    · rw [sptLookup_sptInsert_ne 4 n _ _ isAddress] at found
      by_cases isOffset : n = 6
      · subst n
        rw [sptLookup_sptInsert_same] at found
        have eq := Option.some.inj found
        subst value
        simp [targetPost, StackSemStoreConsts.unsetVarZero, StackSemStateOps.setVar,
          HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL,
          show 3 < k by omega, show 3 ≠ k by omega, show 3 ≠ k+1 by omega,
          offsetPlacement]
      · rw [sptLookup_sptInsert_ne 6 n _ _ isOffset, sptLookup_sptDelete,
          sptLookup_sptDelete] at found
        have notZero : n ≠ 0 := by intro equality; simp [equality] at found
        have notTwo : n ≠ 2 := by intro equality; simp [equality] at found
        simp only [notZero,notTwo,↓reduceIte] at found
        obtain ⟨even,placement⟩ := hloc n value found
        refine ⟨even,?_⟩
        by_cases physical : n / 2 < k
        · rw [if_pos physical] at placement ⊢
          have halfZero : n/2 ≠ 0 := by omega
          have halfOne : n/2 ≠ 1 := by omega
          have halfTwo : n/2 ≠ 2 := by omega
          have halfK : n/2 ≠ k := by omega
          have halfNext : n/2 ≠ k+1 := by omega
          simpa [targetPost, StackSemStoreConsts.unsetVarZero, StackSemStateOps.setVar,
            HolFiniteMapExact.updateEq, HolFiniteMapExact.eraseEq, FUPDATE_HOL, FDOMSUB_HOL,
            halfZero,halfOne,halfTwo,halfK,halfNext] using placement
        · rw [if_neg physical] at placement ⊢
          exact placement

/-- Flapjack infrastructure for the source proof's bitmap-prefix decomposition.
The original index and prefix guards derive both the actual bitmap slice and
its index; no selected-bitmap or target execution fact is assumed. -/
private theorem insertedBitmapSlice {width : Nat} [NeZero width]
    (bs : AppList (BitVec width)) (n : Nat) (words : List (Bool × BitVec width))
    (bitmaps : List (BitVec width))
    (lengthBound : (appListAppend bs).length ≤ n)
    (indexBound : n - (appListAppend bs).length ≤ bitmaps.length)
    (bitmapPrefix : (appListAppend (AppList.append bs
      (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length)))).IsPrefix
      (bitmaps.drop (n - (appListAppend bs).length))) :
    ∃ xs ys, bitmaps = xs ++ Compiler.Backend.WordToStack.constWordsToBitmapW words words.length ++ ys ∧
      xs.length = n := by
  have flatten : appListAppend (AppList.append bs
      (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length))) =
      appListAppend bs ++ Compiler.Backend.WordToStack.constWordsToBitmapW words words.length := by
    rw [(appListAppend_thm bs (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length))
      (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length)).1]
    simp [appListAppend,appendAux]
  rw [flatten] at bitmapPrefix
  obtain ⟨ys, suffix⟩ := bitmapPrefix
  refine ⟨bitmaps.take (n - (appListAppend bs).length) ++ appListAppend bs, ys, ?_, ?_⟩
  · have split := List.take_append_drop (n - (appListAppend bs).length) bitmaps
    rw [← suffix] at split
    simpa only [List.append_assoc] using split.symm
  · simp only [List.length_append, List.length_take, Nat.min_eq_left indexBound]
    omega

/-- Flapjack infrastructure for the actual target StoreConsts run. All its
operands, stub, domain and bitmap premises are derived from the original
simulation guards by the assembling case theorem. -/
private theorem targetSuccess {width : Nat} [NeZero width] {C F : Type}
    (k index : Nat) (address offset : BitVec width) (words : List (Bool × BitVec width))
    (target : StackSemStateFiniteExact width C F) (xs ys : List (BitVec width))
    (large : 4 < k) (storeEnabled : target.useStore = true)
    (allocEnabled : target.useAlloc = true)
    (stub : sptLookup storeConstsStubLocation target.code = some (storeConstsStubNative k))
    (readAddress : target.regs.lookup 2 = some (.word address))
    (readOffset : target.regs.lookup 3 = some (.word offset))
    (bitmapSlice : target.bitmaps = xs ++
      Compiler.Backend.WordToStack.constWordsToBitmapW words words.length ++ ys)
    (indexEq : xs.length = index) (indexBound : index < 2 ^ width)
    (addresses : wordSemConstAddresses address words target.mdomain = true)
    (dimension : goodDimindex width) :
    StackSemEvaluate.evaluate
      (.seq (.inst (.const 1 (BitVec.ofNat width index)))
        (.storeConsts k (k+1) (some storeConstsStubLocation)), target) =
      (none, targetPost k index address offset words target) := by
  have copy := Compiler.Backend.WordToStack.copyWordsCorrect words xs ys address offset
    (fun key => target.mdomain key = true) target.memory (by simpa using addresses) dimension
  rw [← bitmapSlice,indexEq] at copy
  have distinct : [0,1,2,3,k,k+1].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, not_or, and_true, or_false]
    omega
  have stubGuard : StackSemStoreConstsGuard.checkStoreConstsOpt k (k+1)
      (some storeConstsStubLocation) target.code = true := by
    simp [StackSemStoreConstsGuard.checkStoreConstsOpt,stub,
      StackSemStoreConstsGuard.isStoreConstsStub,storeConstsStubNative]
  have prelude : StackSemEvaluate.evaluate
      (.inst (.const 1 (BitVec.ofNat width index)), target) =
      (none,StackSemStateOps.setVar 1 (.word (BitVec.ofNat width index)) target) := by
    simp [StackSemEvaluate.evaluate_inst, StackSemInst.instHOL,
      StackSemIntegerInstructions.instInteger, StackSemExpressions.assign, StackSemExpressions.wordExp]
  rw [StackSemEvaluate.evaluate_seq,prelude]
  simp only [StackSemControl.fixClock,StackSemStateOps.setVar,Nat.min_self]
  rw [StackSemEvaluate.evaluate_storeConsts]
  simp only [storeEnabled,allocEnabled,not_true_eq_false,false_and,
    stubGuard,↓reduceIte,StackSemStoreConsts.storeConstSem,distinct]
  simp only [StackSemStateOps.getVar,HolFiniteMapExact.updateEq,FUPDATE_HOL,
    show (2 : Nat) ≠ 1 by omega, show (3 : Nat) ≠ 1 by omega,readAddress,readOffset]
  have wordIndex : (BitVec.ofNat width index).toNat = index := by
    simp [Nat.mod_eq_of_lt indexBound]
  simp only [wordIndex,copy,↓reduceIte]
  simp only [targetPost,StackSemStateOps.setVar,StackSemStoreConsts.unsetVarZero,
    storeEnabled,allocEnabled]
  rfl


theorem compCorrectStoreConsts {width : Nat} [NeZero width] {C F : Type}
    (ac : Compiler.Encoders.Asm.AsmConfigExact width)
    (first second addressRegister offsetRegister : Nat)
    (words : List (Bool × BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.storeConsts first second addressRegister offsetRegister words) source 0 := by
  intro k f frame post target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [postAllocConventionsHOL,Bool.and_eq_true] at conventions
  have callArgs := conventions.2.2
  have registers : first = 0 ∧ second = 2 ∧ addressRegister = 4 ∧ offsetRegister = 6 := by
    simpa only [callArgConventionHOL,Bool.and_eq_true,beq_iff_eq,and_assoc] using callArgs
  obtain ⟨rfl,rfl,rfl,rfl⟩ := registers
  obtain ⟨address,offset,addressRead,offsetRead,addresses,rfl,postEq⟩ :=
    sourceSuccess 0 2 4 6 words source post result execution notError
  have facts : target.useStore = true ∧ target.useAlloc = true ∧ 4 < k ∧
      sptLookup storeConstsStubLocation target.code = some (storeConstsStubNative k) ∧
      goodDimindex width ∧ target.mdomain = source.mdomain ∧
      target.bitmaps.length < 2 ^ width ∧
      target.regs.lookup 2 = some (.word address) ∧ target.regs.lookup 3 = some (.word offset) := by
    unfold stateRel at related
    obtain ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,h17,h18,
      h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32,h33,h34,h35,h36,
      h37,h38,hloc⟩ := related
    refine ⟨h6,h7,h10,h27,h28,h9,by omega,?_,?_⟩
    · have value := (hloc 4 (.word address) addressRead).2
      simpa only [show 4/2 < k by omega,if_true] using value
    · have value := (hloc 6 (.word offset) offsetRead).2
      simpa only [show 6/2 < k by omega,if_true] using value
  obtain ⟨storeEnabled,allocEnabled,large,stub,dimension,domains,bitmapLength,
    targetAddress,targetOffset⟩ := facts
  have compiledEq : compiled = Compiler.Backend.StackLang.Prog.seq
      (.inst (.const 1 (BitVec.ofNat width n)))
      (.storeConsts k (k+1) (some storeConstsStubLocation)) := by
    have equality := congrArg Prod.fst compilation
    simpa only [compNative,Compiler.Backend.WordToStack.insertBitmap] using equality.symm
  have outputEq : bsPost = AppList.append bs
      (.list (Compiler.Backend.WordToStack.constWordsToBitmapW words words.length)) := by
    have equality := congrArg (fun output => output.2.1) compilation
    simpa only [compNative,Compiler.Backend.WordToStack.insertBitmap] using equality.symm
  subst compiled
  subst bsPost
  obtain ⟨xs,ys,bitmapSlice,indexEq⟩ :=
    insertedBitmapSlice bs n words target.bitmaps lengthBound bitmapBound bitmapPrefix
  have indexBound : n < 2 ^ width := by
    rw [bitmapSlice] at bitmapLength
    simp only [List.length_append] at bitmapLength
    omega
  have targetAddresses : wordSemConstAddresses address words target.mdomain = true := by
    rw [domains]
    exact addresses
  subst post
  refine ⟨0, Nat.le_refl 0,targetPost k n address offset words target,none,?_,?_⟩
  · simpa only [Nat.add_zero] using targetSuccess k n address offset words target xs ys
      large storeEnabled allocEnabled stub targetAddress targetOffset bitmapSlice indexEq
      indexBound targetAddresses dimension
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte,sourcePost] using
      postRelated ac k f frame n address offset words source target lens related offsetRead

end StoreConsts

namespace MoveFull

open Flapjack.WordToStackProofs.CompCorrect.MoveFull

theorem compCorrectMove {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.move priority moves) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨values,distinct,reads,rfl,rfl⟩ :=
    Move.sourceSuccess priority moves source sourcePost result execution notError
  have evens : (∀ n ∈ moves.map Prod.fst, n % 2=0) ∧
      (∀ n ∈ moves.map Prod.snd, n % 2=0) := by
    have raw : (∀ a b, (a,b) ∈ moves → a % 2=0) ∧
        (∀ a b, (a,b) ∈ moves → b % 2=0) := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar,List.all_eq_true] using conventions
    constructor
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.1 a b input
    · intro n member
      obtain ⟨⟨a,b⟩,input,rfl⟩ := List.mem_map.mp member
      exact raw.2 a b input
  have wf : sptWf source.locals=true := by
    unfold stateRel at related
    tauto
  obtain ⟨post,run,relation,_,_⟩ := Move.actualScheduledRun ac k f frame lens moves source target
    related distinct evens.1 evens.2 (by simp [reads]) (by simpa [maxVarHOL] using maxBound)
  rw [Move.scheduledSourceStateReconstruction moves source target k values distinct
    evens.1 evens.2 reads wf] at relation
  have program := congrArg Prod.fst compilation
  simp only [compNative] at program
  subst compiled
  refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
  · simpa only [Nat.add_zero] using run
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,↓reduceIte] using relation

end MoveFull

namespace Inst

open Flapjack.WordToStackProofs.CompCorrect.Inst

private theorem instArgConvention_ofWordLangInst {width : Nat} [NeZero width]
    (i : WordLangInst (BitVec width)) :
    instArgConvention i = instArgConventionExact (HolInst.ofWordLangInst i) := by
  rcases i with _ | ⟨_, _⟩ | ⟨a⟩ | ⟨_, _, _⟩
  all_goals try rfl
  rcases a with ⟨_, _, _, ri⟩ | ⟨_, _, _, ri⟩ | _ | _ | _ | _ | _ | _
  all_goals try rfl
  all_goals (cases ri <;> rfl)

theorem compCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (i : WordLangInst (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.inst i) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, _flat,
    compilation, _lengthBound, _bitmapBound, _bitmapPrefix, _labels, maxBound⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases instRun : WordSemStateFiniteExact.inst i source with _ | post
  · rw [instRun] at execution
    obtain ⟨rfl, -⟩ := Prod.mk.inj execution
    exact absurd rfl notError
  · rw [instRun] at execution
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj execution
    have conventionParts := conventions
    simp only [postAllocConventionsHOL, everyVarHOL, callArgConventionHOL,
      Bool.and_eq_true] at conventionParts
    obtain ⟨physical, _, convention⟩ := conventionParts
    simp only [compNative, Prod.mk.injEq] at compilation
    obtain ⟨rfl, -⟩ := compilation
    obtain ⟨post', run, postRel, _, _⟩ :=
      InstSimulation.evaluateWInst ac (HolInst.ofWordLangInst i) k f frame source post
        target lens (by simpa only [HolInst.to_of] using instRun)
        (by simpa only [HolInst.to_of] using physical)
        (by simpa only [HolInst.to_of, maxVarHOL] using maxBound)
        (by rw [← instArgConvention_ofWordLangInst]; exact convention) related
    refine ⟨0, Nat.le_refl 0, post', none, by simpa using run, ?_⟩
    simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, if_false]
    exact postRel

end Inst

namespace Flat

open Flapjack.WordToStackProofs.CompCorrect.Flat

theorem compCorrectAssign {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : Nat) (expression : WordLangExpHOL (BitVec width)) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.assign name expression) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.assign name expression) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.assign name expression) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.assign name expression) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.assign name expression) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have flat := premises.2.2.2.2.1
  simp only [flatExpConventions, Bool.false_eq_true] at flat

theorem compCorrectStore {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (address : WordLangExpHOL (BitVec width)) (value : Nat) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.store address value) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.store address value) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.store address value) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.store address value) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.store address value) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have flat := premises.2.2.2.2.1
  simp only [flatExpConventions, Bool.false_eq_true] at flat

end Flat

namespace Get

open Flapjack.WordToStackProofs.CompCorrect.Get

theorem compCorrectGet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register : Nat) (name : WordStoreHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.get register name) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  cases read : WordSemStateFiniteExact.getStore name source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have storeRel : source.store = target.store.eraseEq .handler :=
      related.2.2.2.2.2.2.2.2.2.2.2.1
    have targetRead : target.store.lookup (StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name)) = some value := by
      unfold WordSemStateFiniteExact.getStore at read
      rw [storeRel] at read
      cases name <;>
        simp only [storeNameOfWord,StackSemRegisterTransfers.storeOfSyntax,
          HolFiniteMapExact.eraseEq,FDOMSUB_HOL] at read ⊢ <;>
        simp only [reduceCtorEq,ite_false,ite_true] at read <;>
        exact read
    have useStore : target.useStore = true := related.2.2.2.2.2.1
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.get r (storeNameOfWord name),target) =
        (none,StackSemStateOps.setVar r value target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_get,useStore,targetRead]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens value (fun r => .get r (storeNameOfWord name))
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
    · simpa only [Nat.add_zero,← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel

end Get

namespace Set

open Flapjack.WordToStackProofs.CompCorrect.Set

theorem compCorrectSet {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (name : WordStoreHOL)
    (expression : WordLangExpHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.set name expression) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  cases expression <;> simp [flatExpConventions] at flat
  rename_i register
  simp only [WordSemStateFiniteExact.evaluate] at execution
  have notHandler : name ≠ .handler := by
    intro eq; subst name; simp only [true_or,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  have notBitmap : name ≠ .bitmapBase := by
    intro eq; subst name; simp only [or_true,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution; contradiction
  simp only [notHandler,notBitmap,false_or,if_false,WordSemStateFiniteExact.wordExp] at execution
  cases read : WordSemStateFiniteExact.getVar register source with
  | none => simp [read] at execution; obtain ⟨rfl,rfl⟩ := execution; contradiction
  | some value =>
    simp only [read,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,everyVarExpHOL,isPhyVar] using conventions
    rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k,f,frame) with ⟨loads,reg⟩
    obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
      LoadRegister.evaluateWStackLoadWReg1 ac k f frame register reg loads
        source target lens value format even read related
    have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
    have codec : StackSemRegisterTransfers.storeOfSyntax (storeNameOfWord name) = name := by
      cases name <;> rfl
    have programEq := congrArg Prod.fst compilation
    have compiledEq : compiled = wStackLoadNative loads (.set (storeNameOfWord name) reg) := by
      cases name <;> simp only [compNative,format] at programEq <;>
        first | exact programEq.symm | contradiction
    subst compiled
    refine ⟨0, Nat.le_refl 0,StackSemStateOps.setStore name value loaded,none,?_,?_⟩
    · simp only [Nat.add_zero,LoadRegister.evaluateWStackLoadSeq,
        StackSemEvaluate.evaluate_seq,loadRun]
      have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
        have le : loaded.clock ≤ target.clock := by omega
        simp only [StackSemControl.fixClock,Nat.min_eq_right le]
      rw [fix]
      simp only [StackSemEvaluate.evaluate_set,useStore,not_true_eq_false,if_false,
        loadedRead,codec]
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte] using StateRelStoreUpdate.stateRelSetStore ac k f frame source
          loaded lens 0 name value notHandler loadRel

end Set

namespace OpCurrHeap

open Flapjack.WordToStackProofs.CompCorrect.OpCurrHeap

private theorem sourceSuccess {width : Nat} [NeZero width] {C F : Type}
    (source post : WordSemStateFiniteExact width (Nat × C) F)
    (operator : HolBinop) (dst src : Nat) (result : Option (WordSemResult width))
    (execution : WordSemStateFiniteExact.evaluate (.opCurrHeap operator dst src) source = (result,post))
    (notError : result ≠ some .error) :
    ∃ operand heap value : BitVec width,
      WordSemStateFiniteExact.getVar src source = some (.word operand) ∧
      source.store.lookup .currHeap = some (.word heap) ∧
      wordOpHOL operator [operand,heap] = some value ∧
      result = none ∧ post = WordSemStateFiniteExact.setVar dst (.word value) source := by
  cases read : WordSemStateFiniteExact.getVar src source with
  | none =>
    simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
      read,theWords] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  | some operandValue =>
    cases operandValue with
    | loc l n =>
      simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
        read,theWords] at execution
      obtain ⟨rfl,rfl⟩ := execution
      contradiction
    | word operand =>
      cases heapRead : source.store.lookup .currHeap with
      | none =>
        simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
          WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
        obtain ⟨rfl,rfl⟩ := execution
        contradiction
      | some heapValue =>
        cases heapValue with
        | loc l n =>
          simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
            WordSemStateFiniteExact.getStore,read,heapRead,theWords] at execution
          obtain ⟨rfl,rfl⟩ := execution
          contradiction
        | word heap =>
          cases operation : wordOpHOL operator [operand,heap] with
          | none =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            contradiction
          | some value =>
            simp [WordSemStateFiniteExact.evaluate,WordSemStateFiniteExact.wordExp,
              WordSemStateFiniteExact.getStore,read,heapRead,theWords,operation] at execution
            obtain ⟨rfl,rfl⟩ := execution
            exact ⟨operand,heap,value,rfl,rfl,operation,rfl,rfl⟩

theorem compCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (operator : HolBinop) (dst src : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.opCurrHeap operator dst src) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨operand,heap,value,read,heapRead,operation,rfl,rfl⟩ :=
    sourceSuccess source sourcePost operator dst src result execution notError
  have evens : dst % 2 = 0 ∧ src % 2 = 0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  have dstEq : dst = 2*(dst/2) := by omega
  have bound : dst/2 < frame+k := by
    simp only [maxVarHOL] at maxBound
    omega
  rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 src (k,f,frame) with ⟨loads,reg⟩
  obtain ⟨loaded,loadRun,clockEq,loadRel,_,_,_,_,_,loadedRead⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame src reg loads
      source target lens (.word operand) format evens.2 read related
  have storeEq : source.store = loaded.store.eraseEq .handler :=
    loadRel.2.2.2.2.2.2.2.2.2.2.2.1
  have targetHeap : loaded.store.lookup .currHeap = some (.word heap) := by
    rw [storeEq] at heapRead
    simpa [HolFiniteMapExact.eraseEq,FDOMSUB_HOL] using heapRead
  have useStore : loaded.useStore = true := loadRel.2.2.2.2.2.1
  have callback : ∀ d, d ≤ k →
      StackSemEvaluate.evaluate (.opCurrHeap operator d reg,loaded) =
        (none,StackSemStateOps.setVar d (.word value) loaded) := by
    intro d _
    change loaded.regs.lookup reg = some (.word operand) at loadedRead
    simp [StackSemEvaluate.evaluate_opCurrHeap,useStore,StackSemExpressions.wordExp,
      loadedRead,targetHeap,operation]
  obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
    (dst/2) source loaded lens (.word value) (fun d => .opCurrHeap operator d reg)
    loadRel bound callback
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,format] at programEq
  subst compiled
  refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
  · simp only [Nat.add_zero,LoadRegister.evaluateWStackLoadSeq,
      StackSemEvaluate.evaluate_seq,loadRun]
    have fix : StackSemControl.fixClock target ((none : Option (StackSemResult width)),loaded) = (none,loaded) := by
      have le : loaded.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix]
    simpa only [← dstEq] using actual
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte,← dstEq] using postRel

end OpCurrHeap

namespace Clock

open Flapjack.WordToStackProofs.CompCorrect.Clock

theorem compCorrectTick {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate .tick source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k (.tick : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions (.tick : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false .tick (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL (.tick : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have related := premises.2.2.1
  have clocks : source.clock = target.clock := by
    unfold stateRel at related
    exact related.1
  have programEq := congrArg Prod.fst premises.2.2.2.2.2.1
  simp only [compNative] at programEq
  subst compiled
  have execution := premises.1
  rw [WordSemStateFiniteExact.evaluate] at execution
  by_cases zero : source.clock = 0
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨0, Nat.le_refl 0, StackSemStateOps.emptyEnv target, some .timeOut, ?_, ?_⟩
    · change StackSemEvaluate.evaluate (.tick, target) =
        (some .timeOut, StackSemStateOps.emptyEnv target)
      rw [StackSemEvaluate.evaluate_tick, if_pos (clocks.symm.trans zero)]
    · simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
        not_true_eq_false, ↓reduceIte]
      exact ⟨related.2.2.2.1.symm, clocks⟩
  · simp only [zero, ↓reduceIte] at execution
    obtain ⟨resultEq, postEq⟩ := Prod.mk.inj execution
    subst result
    subst sourcePost
    refine ⟨0, Nat.le_refl 0, StackSemStateOps.decClock target, none, ?_, ?_⟩
    · change StackSemEvaluate.evaluate (.tick, target) =
        (none, StackSemStateOps.decClock target)
      have targetNonzero : target.clock ≠ 0 := fun h => zero (clocks.trans h)
      rw [StackSemEvaluate.evaluate_tick, if_neg targetNonzero]
    · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
      exact stateRelDecClock ac k f frame source target lens 0 related

theorem compCorrectMustTerminate {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (body : WordLangProgHOL (BitVec width)) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.mustTerminate body) source = (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k ((.mustTerminate body) : WordLangProgHOL (BitVec width)) = true ∧ flatExpConventions ((.mustTerminate body) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.mustTerminate body) (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.mustTerminate body) : WordLangProgHOL (BitVec width)) < 2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  have related := premises.2.2.1
  unfold stateRel at related
  rcases related with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, termDepth, _⟩
  have execution := premises.1
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [termDepth, ↓reduceDIte] at execution
  have resultEq := (Prod.mk.inj execution).1
  exact False.elim (premises.2.1 resultEq.symm)

end Clock

namespace Return

open Flapjack.WordToStackProofs.CompCorrect.Return

private theorem readAt {width : Nat} [NeZero width] {C F : Type}
    (s : WordSemStateFiniteExact width C F) (ns : List Nat) (xs : List (WordLocW width))
    (h : WordSemStateFiniteExact.getVars ns s = some xs) (i : Nat) :
    xs[i]? = (ns[i]?).bind (fun n => WordSemStateFiniteExact.getVar n s) := by
  induction ns generalizing xs i with
  | nil => simp [WordSemStateFiniteExact.getVars] at h; subst xs; simp
  | cons n ns ih =>
    cases hv : WordSemStateFiniteExact.getVar n s with
    | none => simp [WordSemStateFiniteExact.getVars, hv] at h
    | some v =>
      cases ht : WordSemStateFiniteExact.getVars ns s with
      | none => simp [WordSemStateFiniteExact.getVars, hv, ht] at h
      | some vs =>
        simp only [WordSemStateFiniteExact.getVars, hv, ht, Option.some.injEq] at h
        subst xs
        cases i with
        | zero => simp [hv]
        | succ i => simpa using ih vs ht i

theorem compCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register : Nat) (names : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.return register names) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution, notError, related, conventions, flat,
    compilation, lengthBound, bitmapBound, bitmapPrefix, labels, maximum⟩
  rw [WordSemStateFiniteExact.evaluate] at execution
  cases sourceRead : WordSemStateFiniteExact.getVar register source with
  | none =>
    simp only [sourceRead, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  | some address =>
    cases address with
    | word word =>
      simp only [sourceRead, Prod.mk.injEq] at execution
      exact absurd execution.1.symm notError
    | loc first second =>
      cases sourceValues : WordSemStateFiniteExact.getVars names source with
      | none =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        exact absurd execution.1.symm notError
      | some values =>
        simp only [sourceRead, sourceValues, Prod.mk.injEq] at execution
        obtain ⟨rfl, rfl⟩ := execution
        obtain ⟨even, canonical, nameBound, countBound⟩ := returnFacts related conventions maximum
        rcases format : Compiler.Backend.WordToStackRegFormat.wReg1 register (k, f, frame) with ⟨loads, output⟩
        simp only [compNative, format, Prod.mk.injEq] at compilation
        obtain ⟨rfl, _⟩ := compilation
        obtain ⟨loaded, loadRun, clockSame, loadRelated, stackLength, spaceSame, bitmapSame,
          preserved, outputNotScratch, outputValue⟩ :=
          LoadRegister.evaluateWStackLoadWReg1 ac k f frame register output loads
            source target lens (.loc first second) format even sourceRead related
        let count := Compiler.Backend.WordToStack.numStackRet k names
        let free := Compiler.Backend.WordToStack.skipFree k f frame names
        let post : StackSemStateFiniteExact width C F :=
          {loaded with stackSpace := loaded.stackSpace + free}
        have freeSpace : loaded.stackSpace + free = loaded.stackSpace + f - count := by
          dsimp [free, count, Compiler.Backend.WordToStack.skipFree]
          omega
        have useStack : loaded.useStack = true := loadRelated.2.2.2.2.1
        have frameBound : loaded.stackSpace + f ≤ loaded.stack.length := by
          unfold stateRel at loadRelated
          aesop (config := { enableSimp := false })
        have freeBound : loaded.stackSpace + free ≤ loaded.stack.length := by
          dsimp [free, Compiler.Backend.WordToStack.skipFree]
          omega
        refine ⟨0, Nat.le_refl 0, post, some (.result (.loc first second)), ?_, ?_⟩
        · simp only [Nat.add_zero]
          rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, loadRun]
          simp only [StackSemControl.fixClock, clockSame, Nat.min_self]
          rw [CallHelpers.evaluateSeqStackFree free (.ret output) loaded
            ⟨useStack, by omega⟩]
          rw [StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_stackFree,
            if_neg (by simp [useStack]), if_neg (by omega)]
          simp only [StackSemControl.fixClock, Nat.min_self]
          rw [StackSemEvaluate.evaluate_ret]
          simp only [StackSemStateOps.getVar] at outputValue ⊢
          rw [outputValue]
        · have lengths := WordSemStateFiniteExact.getVarsLengthLemma names source values sourceValues
          have kLarge : 4 < k := related.2.2.2.2.2.2.2.2.2.1
          have extraEq : values.length - (k - 1) = count := by
            dsimp [count, Compiler.Backend.WordToStack.numStackRet]
            omega
          simp only [compCorrectResult, Option.map_some, compileResult,
            ne_eq, not_true_eq_false, ↓reduceIte]
          constructor
          · rw [extraEq]
            have relation := stateRelReturnFlush loadRelated countBound
            simpa only [post, freeSpace] using relation
          · have placements := returnPlacements loadRelated canonical sourceValues countBound
            simpa only [post, freeSpace] using placements

end Return

namespace LocValue

open Flapjack.WordToStackProofs.CompCorrect.LocValue

theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (register location : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.locValue register location) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  simp only [WordSemStateFiniteExact.evaluate] at execution
  by_cases present : sptMem location source.code
  swap
  · simp [present] at execution
    obtain ⟨rfl,rfl⟩ := execution
    contradiction
  · simp only [present,if_true,Prod.mk.injEq] at execution
    obtain ⟨rfl,rfl⟩ := execution
    have even : register % 2 = 0 := by
      simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
        callArgConventionHOL,isPhyVar] using conventions
    have twice : register = 2*(register/2) := by omega
    have bound : register/2 < frame+k := by
      simp only [maxVarHOL] at maxBound
      omega
    have codeDomain : sptDomain target.code =
        (fun n => n=raiseStubLocation ∨ n=storeConstsStubLocation ∨ sptDomain source.code n) :=
      related.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have valid : StackSem.locCheckExact target.code (location,0) := by
      apply Or.inl
      refine ⟨rfl, ?_⟩
      change sptDomain target.code location
      rw [codeDomain]
      exact Or.inr (Or.inr present)
    have run : ∀ r, r ≤ k → StackSemEvaluate.evaluate (.locValue r location 0,target) =
        (none,StackSemStateOps.setVar r (.loc location 0) target) := by
      intro r _
      simp [StackSemEvaluate.evaluate_locValue,valid]
    obtain ⟨post,actual,postRel,_,_⟩ := RegisterWrite.wRegWrite1Thm1 ac k f frame
      (register/2) source target lens (.loc location 0) (fun r => .locValue r location 0)
      related bound run
    have programEq := congrArg Prod.fst compilation
    simp only [compNative] at programEq
    subst compiled
    refine ⟨0, Nat.le_refl 0,post,none,?_,?_⟩
    · simpa only [Nat.add_zero,← twice] using actual
    · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
        ↓reduceIte,← twice] using postRel

end LocValue

namespace Install

open Flapjack.WordToStackProofs.CompCorrect.Install

theorem compCorrectInstall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.install ptr len dptr dlen names) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, hd3, hd4, hc1, hc2⟩ :=
    installConventions k ptr len dptr dlen names conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 dptr (k, f, frame) with ⟨xs, reg3⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 dlen (k, f, frame) with ⟨ys, reg4⟩
  have programEq := congrArg Prod.fst compilation
  simp only [compNative, fmt1, fmt2] at programEq
  subst compiled
  -- The source run.
  rw [WordSemStateFiniteExact.evaluate] at execution
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w1 | ⟨_, _⟩) <;>
    rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h3 : WordSemStateFiniteExact.getVar dptr source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h5 : WordSemStateFiniteExact.getVar dlen source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h2, h4, h3, h5, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hor : source.compileOracle 0 with ⟨⟨bm0, cfg⟩, progs⟩
  simp only [hor] at execution
  rcases hcf : wordSemBufferFlush source.codeBuffer w1 w2 with _ | ⟨bytes, cb⟩ <;>
    rcases hdf : wordSemBufferFlush source.dataBuffer w3 w4 with _ | ⟨data, db⟩ <;>
    simp only [hcf, hdf, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rcases hsc : source.compile (bm0, cfg) progs with _ | ⟨bytes', data', cfg'⟩ <;>
    rcases progs with _ | ⟨⟨kk, argc, prog⟩, rest⟩ <;>
    simp only [hsc, Prod.mk.injEq] at execution <;>
    try first
      | exact absurd execution.1.symm notError
      | exact absurd (congrArg Prod.fst execution).symm notError
  by_cases hcond : bytes = bytes' ∧ data = data' ∧
      (holShiftSeq 1 source.compileOracle 0).1 = cfg'
  swap
  · rw [if_neg hcond] at execution
    exact absurd (congrArg Prod.fst execution).symm notError
  rw [if_pos hcond] at execution
  simp only [Prod.mk.injEq] at execution
  obtain ⟨rfl, rfl⟩ := execution
  -- The target loads of the data pointer and length.
  obtain ⟨t1, run1, clock1, rel1, -, -, -, -, regNe, loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame dptr reg3 xs source target lens
      (.word w3) fmt1 hd3 h3 related
  obtain ⟨t2, run2, clock2, -, rel2, -, -, otherReads, -, loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame dlen reg4 ys source t1 lens
      (.word w4) fmt2 hd4 h5 rel1
  have r10 : 4 < k := rel2.2.2.2.2.2.2.2.2.2.1
  have read1 : StackSemStateOps.getVar 1 t2 = some (.word w1) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 2 _
      ⟨rel2, h2, rfl, by omega⟩
    simpa using this
  have read2 : StackSemStateOps.getVar 2 t2 = some (.word w2) := by
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source t2 lens 0 4 _
      ⟨rel2, h4, rfl, by omega⟩
    simpa using this
  have read3 : StackSemStateOps.getVar reg3 t2 = some (.word w3) := by
    rw [otherReads reg3 regNe]; exact loaded1
  -- The target compiler and oracle on the installed programs.
  have rel2' := rel2
  unfold stateRel at rel2'
  obtain ⟨-, -, -, -, r5, -, -, -, -, -, -, -, -, -, -, -, -, -, r19, r20, r21, r22, -⟩ := rel2'
  rcases hcw : compileWordToStackNative ac false k ((kk, argc, prog) :: rest) (.nil, bm0) with
    ⟨progs2, fs, bm⟩
  have hsc' := hsc
  rw [r21] at hsc'
  simp only [hcw] at hsc'
  rcases htc : t2.compile cfg progs2 with _ | ⟨bytes2, cfg2⟩
  · simp [htc] at hsc'
  simp only [htc, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsc'
  obtain ⟨rfl, rfl, rfl⟩ := hsc'
  have hor2 : t2.compileOracle 0 = (cfg, progs2, appListAppend bm.1) := by
    rw [r22]; simp only [hor, hcw]
  have hmap := mapFstCompileWordToStack ac false k _ _ _ _ hcw
  rcases progs2 with _ | ⟨⟨kk2, prog2⟩, rest2⟩
  · simp at hmap
  simp only [List.map_cons, List.cons.injEq] at hmap
  obtain ⟨rfl, -⟩ := hmap
  have hflush : wordSemBufferFlush source.dataBuffer w3 w4 = some (data, db) := hdf
  have hdata : source.dataBuffer.buffer = appListAppend bm.1 := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [hflush.1, hcond.2.1]
    · cases hflush
  have hdb : db.buffer = [] ∧ db.spaceLeft = source.dataBuffer.spaceLeft := by
    unfold wordSemBufferFlush at hflush
    split at hflush
    · simp only [Option.some.injEq, Prod.mk.injEq] at hflush
      rw [← hflush.2]; exact ⟨rfl, rfl⟩
    · cases hflush
  have hcfg : (source.compileOracle 1).1 = (bm.2, cfg2) := hcond.2.2
  have hnew : (holShiftSeq 1 t2.compileOracle 0).1 = cfg2 := by
    show (t2.compileOracle 1).1 = cfg2
    rcases hso : source.compileOracle 1 with ⟨⟨b1, c1⟩, ps⟩
    rw [r22]
    simp only [hso]
    rw [hso] at hcfg
    simp only [Prod.mk.injEq] at hcfg
    rcases compileWordToStackNative ac false k ps (.nil, b1) with ⟨a, b, c⟩
    exact hcfg.2
  -- The target run and the related post-states.
  refine ⟨0, Nat.le_refl 0, { t2 with
      bitmaps := t2.bitmaps ++ appListAppend bm.1
      codeBuffer := cb
      dataBuffer := db
      code := sptUnion t2.code (sptFromAList ((kk2, prog2) :: rest2))
      regs := (StackSemStateOps.restrictIn t2.regs t2.ffiSaveRegs).updateEq (1, .loc kk2 0)
      fpRegs := HolFiniteMapExact.empty
      compileOracle := holShiftSeq 1 t2.compileOracle }, none, ?_, ?_⟩
  · simp only [Nat.add_zero, wStackLoadAppend, Function.comp_apply,
      show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)), t1) =
        (none, t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq, StackSemEvaluate.evaluate_seq, run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)), t2) =
        (none, t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock, Nat.min_eq_right le]
    simp only [fix2]
    rw [StackSemEvaluate.evaluate_install]
    simp only [read1, read2, read3, loaded2, hor2, r20, r19, r5, hcf, hflush, if_true, htc]
    rw [if_pos ⟨hcond.1, hcond.2.1.trans (congrArg (fun x => x.2.2) hor2).symm, hnew⟩]
  · simp only [compCorrectResult, Option.map_none, ne_eq, not_true_eq_false, ↓reduceIte]
    exact installRelation ac k f frame source t2 lens rel2 names hc1 hc2 env hce bm0 cfg kk2 argc
      prog rest hor (_ :: rest2) fs bm hcw cfg2 hcfg cb db hdata hdb

end Install

namespace CodeBufferWrite

open Flapjack.WordToStackProofs.CompCorrect.CodeBufferWrite

theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.codeBufferWrite r1 r2) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.codeBuffer = source.codeBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨0, Nat.le_refl 0,{t2 with codeBuffer := cb},none,?_,?_⟩
  · simp only [Nat.add_zero,wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    simp only [StackSemEvaluate.evaluate_codeBufferWrite,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using codeBufferRelation cb rel2

end CodeBufferWrite

namespace DataBufferWrite

open Flapjack.WordToStackProofs.CompCorrect.DataBufferWrite

theorem compCorrectDataBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (r1 r2 : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F) :
    SimulationB ac (.dataBufferWrite r1 r2) source 0 := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  rcases premises with ⟨execution,notError,related,conventions,flat,compilation,
    lengthBound,bitmapBound,bitmapPrefix,labels,maxBound⟩
  obtain ⟨w1,w2,cb,read1,read2,writeEq,rfl,rfl⟩ :=
    sourceSuccess r1 r2 source sourcePost result execution notError
  have evens : r1%2=0 ∧ r2%2=0 := by
    simpa [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,isPhyVar] using conventions
  rcases fmt1 : Compiler.Backend.WordToStackRegFormat.wReg1 r1 (k,f,frame) with ⟨xs,reg1⟩
  rcases fmt2 : Compiler.Backend.WordToStackRegFormat.wReg2 r2 (k,f,frame) with ⟨ys,reg2⟩
  obtain ⟨t1,run1,clock1,rel1,_,_,_,_,regNe,loaded1⟩ :=
    LoadRegister.evaluateWStackLoadWReg1 ac k f frame r1 reg1 xs source target lens
      (.word w1) fmt1 evens.1 read1 related
  obtain ⟨t2,run2,clock2,_,rel2,_,_,otherReads,_,loaded2⟩ :=
    LoadRegisterTwo.evaluateWStackLoadWReg2 ac k f frame r2 reg2 ys source t1 lens
      (.word w2) fmt2 evens.2 read2 rel1
  have read1Final : StackSemStateOps.getVar reg1 t2 = some (.word w1) := by
    rw [otherReads reg1 regNe]
    exact loaded1
  have bufferEq : t2.dataBuffer = source.dataBuffer :=
    rel2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have capacity : cb.buffer.length+cb.spaceLeft = source.dataBuffer.buffer.length+source.dataBuffer.spaceLeft := by
    unfold wordSemBufferWrite at writeEq
    split at writeEq
    · rename_i guard
      have equal := Option.some.inj writeEq
      subst cb
      simp only [List.length_append,List.length_singleton]
      omega
    · cases writeEq
  have programEq := congrArg Prod.fst compilation
  simp only [compNative,fmt1,fmt2] at programEq
  subst compiled
  refine ⟨0, Nat.le_refl 0,{t2 with dataBuffer := cb},none,?_,?_⟩
  · simp only [Nat.add_zero,wStackLoadAppend,Function.comp_apply]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run1]
    have fix1 : StackSemControl.fixClock target ((none : Option (StackSemResult width)),t1) = (none,t1) := by
      have le : t1.clock ≤ target.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix1]
    rw [LoadRegister.evaluateWStackLoadSeq,StackSemEvaluate.evaluate_seq,run2]
    have fix2 : StackSemControl.fixClock t1 ((none : Option (StackSemResult width)),t2) = (none,t2) := by
      have le : t2.clock ≤ t1.clock := by omega
      simp only [StackSemControl.fixClock,Nat.min_eq_right le]
    simp only [fix2]
    have useStack : t2.useStack = true := rel2.2.2.2.2.1
    simp only [StackSemEvaluate.evaluate_dataBufferWrite,useStack,not_true_eq_false,if_false,read1Final,loaded2,bufferEq,writeEq]
  · simpa only [compCorrectResult,Option.map_none,ne_eq,not_true_eq_false,
      ↓reduceIte] using dataBufferRelation cb capacity rel2

end DataBufferWrite

namespace FFI

open Flapjack.WordToStackProofs.CompCorrect.FFI

theorem compCorrectFFI {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (index : Basis.Pure.MlString.MlString)
    (ptr1 len1 ptr2 len2 : Nat) (names : WordLangCutsetsHOL) (k f frame : Nat)
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    (premises : WordSemStateFiniteExact.evaluate (.ffi index ptr1 len1 ptr2 len2 names) source =
        (result, sourcePost) ∧
      result ≠ some .error ∧ stateRel ac k f frame source target lens 0 ∧
      postAllocConventionsHOL k
        ((.ffi index ptr1 len1 ptr2 len2 names) : WordLangProgHOL (BitVec width)) = true ∧
      flatExpConventions
        ((.ffi index ptr1 len1 ptr2 len2 names) : WordLangProgHOL (BitVec width)) = true ∧
      compNative ac false (.ffi index ptr1 len1 ptr2 len2 names) (bs, n) (k, f, frame) =
        (compiled, (bsPost, nPost)) ∧
      (appListAppend bs).length ≤ n ∧
      n - (appListAppend bs).length ≤ target.bitmaps.length ∧
      List.IsPrefix (appListAppend bsPost) (target.bitmaps.drop (n - (appListAppend bs).length)) ∧
      (∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) ∧
      maxVarHOL ((.ffi index ptr1 len1 ptr2 len2 names) : WordLangProgHOL (BitVec width)) <
        2 * frame + 2 * k) :
    ∃ (extraClock : Nat), extraClock ≤ 0 ∧ ∃ (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens := by
  obtain ⟨execution, notError, related, conventions, -, compilation, -, -, -, -, -⟩ := premises
  obtain ⟨rfl, rfl, rfl, rfl, hc1, hc2⟩ :=
    ffiConventions k index ptr1 len1 ptr2 len2 names conventions
  simp only [compNative, Prod.mk.injEq] at compilation
  obtain ⟨rfl, -⟩ := compilation
  have htarget : {target with clock := target.clock + 0} = target := by simp
  refine ⟨0, Nat.le_refl 0, ?_⟩
  rw [htarget]
  have related' := related
  unfold stateRel at related'
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, r16, r17, r18,
    r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35, r36,
    r37, r38, rloc⟩ := related'
  have hvar : ∀ m v, WordSemStateFiniteExact.getVar (2 * m) source = some v → m < k →
      StackSemStateOps.getVar m target = some v := by
    intro m v hm hlt
    have := StateRelGetVar.stateRelGetVarImp' ac k f frame source target lens 0 (2 * m) v
      ⟨related, hm, by omega, by omega⟩
    rwa [show 2 * m / 2 = m by omega] at this
  rw [WordSemStateFiniteExact.evaluate] at execution
  rw [StackSemEvaluate.evaluate_ffi]
  simp only [show (2 : Nat) / 2 = 1 by rfl, show (4 : Nat) / 2 = 2 by rfl,
    show (6 : Nat) / 2 = 3 by rfl, show (8 : Nat) / 2 = 4 by rfl]
  rcases h4 : WordSemStateFiniteExact.getVar 4 source with _ | (w | ⟨_, _⟩) <;>
    rcases h2 : WordSemStateFiniteExact.getVar 2 source with _ | (w2 | ⟨_, _⟩) <;>
    rcases h8 : WordSemStateFiniteExact.getVar 8 source with _ | (w3 | ⟨_, _⟩) <;>
    rcases h6 : WordSemStateFiniteExact.getVar 6 source with _ | (w4 | ⟨_, _⟩) <;>
    simp only [h4, h2, h8, h6, Prod.mk.injEq] at execution <;>
    try exact absurd execution.1.symm notError
  rw [hvar 2 _ h4 (by omega), hvar 1 _ h2 (by omega), hvar 4 _ h8 (by omega),
    hvar 3 _ h6 (by omega)]
  simp only [r8, r9, r15, r4]
  rcases hce : wordSemCutEnv names source.locals with _ | env
  · simp only [hce, Prod.mk.injEq] at execution
    exact absurd execution.1.symm notError
  simp only [hce] at execution
  rcases hr1 : readBytearrayWordHOL w2 w.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes <;>
    rcases hr2 : readBytearrayWordHOL w4 w3.toNat
      (memLoadByteAuxExact source.memory source.mdomain source.be) with _ | bytes2 <;>
    simp only [hr1, hr2, Prod.mk.injEq] at execution ⊢ <;>
    try exact absurd execution.1.symm notError
  rcases hcall : callFFIHOL source.ffi (.extCall index) bytes bytes2 with ⟨newFfi, newBytes⟩ | outcome <;>
    simp only [hcall, Prod.mk.injEq] at execution ⊢ <;> obtain ⟨rfl, rfl⟩ := execution
  · refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_none, ne_eq, not_true_eq_false, if_false]
    have henv : env = sptUnion (sptInter source.locals names.2) (sptInter source.locals names.1) := by
      unfold wordSemCutEnv at hce
      rcases hcs : wordSemCutEnvs names source.locals with _ | ⟨e1, e2⟩
      · rw [hcs] at hce; cases hce
      rw [hcs] at hce
      obtain ⟨he1, he2⟩ := AllocStateRel.cutEnvs_eq hcs
      simp only [Option.some.injEq] at hce he1 he2
      rw [← hce, ← he1, ← he2]
    unfold stateRel
    refine ⟨r1, r2, r3, rfl, r5, r6, r7, rfl, rfl, r10, r11, r12, r13, r14, rfl, rfl, r17, rfl,
      r19, r20, r21, r22, r23, r24, r25, r26, r27, r28, r29, r30, r31, r32, r33, r34, r35,
      ?_, r37, r38, ?_⟩
    · show sptWf env = true
      rw [henv]
      exact sptWfUnion _ _ ⟨sptWfInter _ _, sptWfInter _ _⟩
    · intro m v hm
      change sptLookup m env = some v at hm
      rw [henv, sptLookup_sptUnion, sptLookup_sptInterCases, sptLookup_sptInterCases] at hm
      have hlook : sptLookup m source.locals = some v ∧
          (sptDomain names.1 m ∨ sptDomain names.2 m) := by
        unfold sptDomain
        revert hm
        cases sptLookup m source.locals <;> cases sptLookup m names.2 <;>
          cases sptLookup m names.1 <;> simp
      obtain ⟨hl, hd⟩ := hlook
      have hev : m % 2 = 0 ∧ 2 * k ≤ m := hd.elim (hc1 m) (hc2 m)
      obtain ⟨he, hif⟩ := rloc m v hl
      refine ⟨he, ?_⟩
      rw [if_neg (by omega)] at hif ⊢
      exact hif
  · refine ⟨_, _, ⟨rfl, rfl⟩, ?_⟩
    unfold compCorrectResult
    simp only [Option.map_some, compileResult, ne_eq, not_true_eq_false, if_false]
    exact ⟨r4.symm, r1⟩

end FFI





















end InitECandidate.Solver.Wave8Stage.WordToStackZeroClock
