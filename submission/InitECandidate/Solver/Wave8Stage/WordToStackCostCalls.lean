import InitECandidate.Solver.Wave8Stage.WordToStackCostComposition
import InitECandidate.Solver.Wave8Stage.WordToStackCallClock

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.WordToStackCostCalls
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Encoders.Asm
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open InitECandidate.Solver.Wave8Stage.WordToStackBounded
open InitECandidate.Solver.Wave8Stage.WordToStackSourceCost

private theorem tailWithBudget {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F) (budget : Nat)
    (ih : ∀ xs args1 prog ss,
      getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs)
        source.code source.stackSize = some (args1,prog,ss) ∧
      handler = none ∧ source.clock ≠ 0 →
      SimulationB ac prog (callEnv args1 ss (WordSemStateFiniteExact.decClock source)) budget) :
    SimulationB ac (.call none dest args handler) source budget := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens premises
  exact WordToStackTailClock.compCorrectCallTail ac dest args handler source budget ih
    k f frame sourcePost target result bs bsPost n nPost compiled lens premises

theorem compCorrectCallTail {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : ∀ xs args1 prog ss,
      getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs)
        source.code source.stackSize = some (args1,prog,ss) ∧
      handler = none ∧ source.clock ≠ 0 →
      SimulationB ac prog (callEnv args1 ss (WordSemStateFiniteExact.decClock source))
        (sourceCost prog (callEnv args1 ss (WordSemStateFiniteExact.decClock source)))) :
    SimulationB ac (.call none dest args handler) source
      (sourceCost (.call none dest args handler) source) := by
  classical
  rw [sourceCost]
  split
  · rename_i get
    apply tailWithBudget
    intro xs args1 prog ss facts
    rw [get] at facts
    cases facts.1
  · rename_i xs get
    split
    · rename_i found
      apply tailWithBudget
      intro xsAgain args1 prog ss facts
      have same : xsAgain = xs := Option.some.inj (facts.1.symm.trans get)
      subst xsAgain
      rw [found] at facts
      cases facts.2.2.1
    · rename_i args1 prog ss found
      split
      · rename_i zero
        apply tailWithBudget
        intro xsAgain argsAgain progAgain ssAgain facts
        exact False.elim (facts.2.2.2.2 zero)
      · rename_i nonzero
        cases handler with
        | none =>
          apply tailWithBudget
          intro xsAgain argsAgain progAgain ssAgain facts
          have same : xsAgain = xs := Option.some.inj (facts.1.symm.trans get)
          subst xsAgain
          have sameCode := Option.some.inj (facts.2.2.1.symm.trans found)
          obtain ⟨rfl, pair⟩ := Prod.mk.inj sameCode
          obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
          exact ih xs argsAgain progAgain ssAgain facts
        | some descriptor =>
          apply tailWithBudget
          intro xsAgain argsAgain progAgain ssAgain facts
          cases facts.2.2.2.1

def ReturnInductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    SimulationB ac retCode (WordSemStateFiniteExact.setVars values ys popped)
      (sourceCost retCode (WordSemStateFiniteExact.setVars values ys popped))) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    SimulationB ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source)))
      (sourceCost prog (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source)))))


private theorem returningImpossible {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (impossible : ∀ xs args1 prog ss envs,
      CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
      source.clock ≠ 0 → False) :
    SimulationB ac (.call (some (values,names,retCode,l1,l2)) dest args none) source 0 := by
  apply WordToStackReturnClock.compCorrectCallReturningNone
    (bodyBudget := 0) (returnBudget := 0)
  constructor
  · intro xs args1 prog ss envs location ys calleePost popped facts
    exact False.elim (impossible xs args1 prog ss envs ⟨facts.1,facts.2.1⟩)
  · intro xs args1 prog ss envs facts
    exact False.elim (impossible xs args1 prog ss envs facts)

theorem compCorrectCallReturningNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : ReturnInductionHypotheses ac values names retCode l1 l2 dest args source) :
    SimulationB ac (.call (some (values,names,retCode,l1,l2)) dest args none) source
      (sourceCost (.call (some (values,names,retCode,l1,l2)) dest args none) source) := by
  classical
  cases get : getVars args source with
  | none =>
    rw [sourceCost, get]
    apply returningImpossible
    intro xs args1 prog ss envs facts
    have guard := facts.1.1
    rw [get] at guard
    cases guard
  | some xs =>
    cases found : wordSemFindCode dest
        (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize with
    | none =>
      rw [sourceCost]
      simp only [get, found]
      apply returningImpossible
      intro xsAgain args1 prog ss envs facts
      have same : xsAgain = xs := Option.some.inj (facts.1.1.symm.trans get)
      subst xsAgain
      have guard := facts.1.2.2.1
      rw [found] at guard
      cases guard
    | some descriptor =>
      obtain ⟨args1,prog,ss⟩ := descriptor
      by_cases zero : source.clock = 0
      · rw [sourceCost]
        simp only [get, found, dif_pos zero]
        apply returningImpossible
        intro xsAgain argsAgain progAgain ssAgain envs facts
        exact facts.2 zero
      · cases cut : wordSemCutEnvs names source.locals with
        | none =>
          rw [sourceCost]
          simp only [get, found, dif_neg zero]
          rw [cut]
          apply returningImpossible
          intro xsAgain argsAgain progAgain ssAgain envs facts
          have guard := facts.1.2.2.2.2
          rw [cut] at guard
          cases guard
        | some envs =>
          rcases run : evaluate prog
              (callEnv args1 ss (pushEnv envs none (WordSemStateFiniteExact.decClock source))) with
            ⟨result,post⟩
          rw [sourceCost]
          simp only [get, found, dif_neg zero]
          simp only [cut, run]
          simp only [Nat.max_zero]
          apply WordToStackReturnClock.compCorrectCallReturningNone
          have identify : ∀ xsAgain argsAgain progAgain ssAgain envsAgain,
              CallReturning.SourceGuards values names retCode l1 l2 dest args source
                xsAgain argsAgain progAgain ssAgain envsAgain →
              xsAgain = xs ∧ argsAgain = args1 ∧ progAgain = prog ∧ ssAgain = ss ∧ envsAgain = envs := by
            intro xsAgain argsAgain progAgain ssAgain envsAgain guards
            have sameXs := Option.some.inj (guards.1.symm.trans get)
            subst xsAgain
            have sameCode := Option.some.inj (guards.2.2.1.symm.trans found)
            obtain ⟨rfl, pair⟩ := Prod.mk.inj sameCode
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
            have sameEnvs := Option.some.inj (guards.2.2.2.2.symm.trans cut)
            exact ⟨rfl,rfl,rfl,rfl,sameEnvs⟩
          constructor
          · intro xsAgain argsAgain progAgain ssAgain envsAgain location ys calleePost popped facts
            have selected := ih.1 xsAgain argsAgain progAgain ssAgain envsAgain
              location ys calleePost popped facts
            obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := identify _ _ _ _ _ facts.1
            have sameRun := Prod.mk.inj (facts.2.2.1.symm.trans run)
            obtain ⟨rfl,rfl⟩ := sameRun
            have actualPop := facts.2.2.2.2.1
            have postEq := congrArg Prod.snd facts.2.2.1
            dsimp only at postEq
            rw [← postEq] at actualPop
            dsimp only
            split
            · rename_i missing
              rw [missing] at actualPop
              cases actualPop
            · rename_i poppedAgain foundPop
              have same : poppedAgain = popped := Option.some.inj (foundPop.symm.trans actualPop)
              subst poppedAgain
              exact selected
          · intro xsAgain argsAgain progAgain ssAgain envsAgain facts
            have selected := ih.2 xsAgain argsAgain progAgain ssAgain envsAgain facts
            obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := identify _ _ _ _ _ facts.1
            exact selected

def HandlerInductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    SimulationB ac retCode (WordSemStateFiniteExact.setVars values ys popped) (sourceCost retCode (WordSemStateFiniteExact.setVars values ys popped))) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location value : WordLocW width)
    (calleePost : WordSemStateFiniteExact width (Nat × C) F),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),calleePost) ∧
    ¬ location ≠ .loc h1 h2 ∧
    sptDomainEqUnion calleePost.locals envs.1 envs.2 →
    SimulationB ac handlerCode (WordSemStateFiniteExact.setVar handlerVar value calleePost) (sourceCost handlerCode (WordSemStateFiniteExact.setVar handlerVar value calleePost))) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    SimulationB ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) (sourceCost prog (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source)))))


private theorem handlerImpossible {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (impossible : ∀ xs args1 prog ss envs,
      CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
      source.clock ≠ 0 → False) :
    SimulationB ac (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source 0 := by
  apply WordToStackHandlerClock.compCorrectCallReturningHandler
    (bodyBudget := 0) (returnBudget := 0) (handlerBudget := 0)
  refine ⟨?_,?_,?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    exact False.elim (impossible xs args1 prog ss envs ⟨facts.1,facts.2.1⟩)
  · intro xs args1 prog ss envs location value calleePost facts
    exact False.elim (impossible xs args1 prog ss envs ⟨facts.1,facts.2.1⟩)
  · intro xs args1 prog ss envs facts
    exact False.elim (impossible xs args1 prog ss envs facts)

theorem compCorrectCallReturningHandler {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : HandlerInductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source) :
    SimulationB ac (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source
      (sourceCost (.call (some (values,names,retCode,l1,l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source) := by
  classical
  cases get : getVars args source with
  | none =>
    rw [sourceCost, get]
    apply handlerImpossible
    intro xs args1 prog ss envs facts
    have guard := facts.1.1
    rw [get] at guard
    cases guard
  | some xs =>
    cases found : wordSemFindCode dest
        (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize with
    | none =>
      rw [sourceCost]
      simp only [get, found]
      apply handlerImpossible
      intro xsAgain args1 prog ss envs facts
      have same : xsAgain = xs := Option.some.inj (facts.1.1.symm.trans get)
      subst xsAgain
      have guard := facts.1.2.2.1
      rw [found] at guard
      cases guard
    | some descriptor =>
      obtain ⟨args1,prog,ss⟩ := descriptor
      by_cases zero : source.clock = 0
      · rw [sourceCost]
        simp only [get, found, dif_pos zero]
        apply handlerImpossible
        intro xsAgain argsAgain progAgain ssAgain envs facts
        exact facts.2 zero
      · cases cut : wordSemCutEnvs names source.locals with
        | none =>
          rw [sourceCost]
          simp only [get, found, dif_neg zero]
          rw [cut]
          apply handlerImpossible
          intro xsAgain argsAgain progAgain ssAgain envs facts
          have guard := facts.1.2.2.2.2
          rw [cut] at guard
          cases guard
        | some envs =>
          rcases run : evaluate prog
              (callEnv args1 ss (pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) with
            ⟨result,post⟩
          rw [sourceCost]
          simp only [get, found, dif_neg zero]
          simp only [cut, run]
          apply WordToStackHandlerClock.compCorrectCallReturningHandler
          have identify : ∀ xsAgain argsAgain progAgain ssAgain envsAgain,
              CallReturning.SourceGuards values names retCode l1 l2 dest args source
                xsAgain argsAgain progAgain ssAgain envsAgain →
              xsAgain = xs ∧ argsAgain = args1 ∧ progAgain = prog ∧ ssAgain = ss ∧ envsAgain = envs := by
            intro xsAgain argsAgain progAgain ssAgain envsAgain guards
            have sameXs := Option.some.inj (guards.1.symm.trans get)
            subst xsAgain
            have sameCode := Option.some.inj (guards.2.2.1.symm.trans found)
            obtain ⟨rfl, pair⟩ := Prod.mk.inj sameCode
            obtain ⟨rfl,rfl⟩ := Prod.mk.inj pair
            have sameEnvs := Option.some.inj (guards.2.2.2.2.symm.trans cut)
            exact ⟨rfl,rfl,rfl,rfl,sameEnvs⟩
          refine ⟨?_,?_,?_⟩
          · intro xsAgain argsAgain progAgain ssAgain envsAgain location ys calleePost popped facts
            have selected := ih.1 xsAgain argsAgain progAgain ssAgain envsAgain
              location ys calleePost popped facts
            obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := identify _ _ _ _ _ facts.1
            have sameRun := Prod.mk.inj (facts.2.2.1.symm.trans run)
            obtain ⟨rfl,rfl⟩ := sameRun
            have actualPop := facts.2.2.2.2.1
            have postEq := congrArg Prod.snd facts.2.2.1
            dsimp only at postEq
            rw [← postEq] at actualPop
            dsimp only
            split
            · rename_i missing
              rw [missing] at actualPop
              cases actualPop
            · rename_i poppedAgain foundPop
              have same : poppedAgain = popped := Option.some.inj (foundPop.symm.trans actualPop)
              subst poppedAgain
              exact selected
          · intro xsAgain argsAgain progAgain ssAgain envsAgain location value calleePost facts
            have selected := ih.2.1 xsAgain argsAgain progAgain ssAgain envsAgain
              location value calleePost facts
            obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := identify _ _ _ _ _ facts.1
            have sameRun := Prod.mk.inj (facts.2.2.1.symm.trans run)
            obtain ⟨rfl,rfl⟩ := sameRun
            simpa only [facts.2.2.1] using selected
          · intro xsAgain argsAgain progAgain ssAgain envsAgain facts
            have selected := ih.2.2 xsAgain argsAgain progAgain ssAgain envsAgain facts
            obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := identify _ _ _ _ _ facts.1
            exact selected

def OriginalInductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    : Prop :=
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc originalL1 originalL2 ∨ ys.length ≠ n.length) ∧
        WordSemStateFiniteExact.popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      SimulationB ac retHandler (WordSemStateFiniteExact.setVars n ys s1) (sourceCost retHandler (WordSemStateFiniteExact.setVars n ys s1))) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x' y v n' v2 h
        v4 originalL1' originalL2',
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ handler = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (originalL1', originalL2') ∧ x' = .loc originalL1' originalL2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
      SimulationB ac h (WordSemStateFiniteExact.setVar n' y s2) (sourceCost h (WordSemStateFiniteExact.setVar n' y s2))) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      SimulationB ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) (sourceCost prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))))) ∧
    (∀ xs v3 args1 v10 prog ss,
      WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
      v3 = (args1,v10) ∧ v10 = (prog,ss) ∧ ret = none ∧ handler = none ∧ source.clock ≠ 0 →
      SimulationB ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)) (sourceCost prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source))))

theorem inductionHypothesesOfOriginal {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (original :
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc originalL1 originalL2 ∨ ys.length ≠ n.length) ∧
        WordSemStateFiniteExact.popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      SimulationB ac retHandler (WordSemStateFiniteExact.setVars n ys s1) (sourceCost retHandler (WordSemStateFiniteExact.setVars n ys s1))) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x' y v n' v2 h
        v4 originalL1' originalL2',
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .exception x' y ∧ (some (handlerVar,handlerCode,h1,h2)) = some v ∧ v = (n', v2) ∧ v2 = (h, v4) ∧
        v4 = (originalL1', originalL2') ∧ x' = .loc originalL1' originalL2' ∧ sptDomainEqUnion s2.locals envs.1 envs.2 →
      SimulationB ac h (WordSemStateFiniteExact.setVar n' y s2) (sourceCost h (WordSemStateFiniteExact.setVar n' y s2))) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      SimulationB ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) (sourceCost prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source)))))) :
    HandlerInductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode
      source := by
  refine ⟨?_,?_,?_⟩
  · intro xs args1 prog ss envs location ys calleePost popped facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock,run,checked,pop,domain⟩
    exact original.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs (some (.result location ys)) calleePost
      (.result location ys) location ys popped
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock,run,rfl,rfl,checked,pop,domain⟩
  · intro xs args1 prog ss envs location value calleePost facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock,run,checked,domain⟩
    exact original.2.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs (some (.exception location value)) calleePost
      (.exception location value) location value (handlerVar,handlerCode,h1,h2)
      handlerVar (handlerCode,h1,h2) handlerCode (h1,h2) h1 h2
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock,run,rfl,rfl,rfl,rfl,
        rfl,rfl,by simpa only [not_ne_iff] using checked,domain⟩
  · intro xs args1 prog ss envs facts
    rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock⟩
    exact original.2.2 xs (args1,prog,ss) args1 (prog,ss) prog ss
      (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
      retCode (l1,l2) l1 l2 envs
      ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock⟩

theorem returningCallCase {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : OriginalInductionHypotheses ac (some (values,names,retCode,l1,l2)) dest args handler source
) :
    SimulationB ac (.call (some (values,names,retCode,l1,l2)) dest args handler) source
      (sourceCost (.call (some (values,names,retCode,l1,l2)) dest args handler) source) := by
  cases handler with
  | none =>
    apply compCorrectCallReturningNone ac values names retCode l1 l2 dest args source
    refine ⟨?_,?_⟩
    · intro xs args1 prog ss envs location ys calleePost popped facts
      rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock,run,checked,pop,domain⟩
      exact ih.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
        (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
        retCode (l1,l2) l1 l2 envs (some (.result location ys)) calleePost
        (.result location ys) location ys popped
        ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock,run,rfl,rfl,checked,pop,domain⟩
    · intro xs args1 prog ss envs facts
      rcases facts with ⟨⟨get,bad,find,valid,cut⟩,clock⟩
      exact ih.2.2.1 xs (args1,prog,ss) args1 (prog,ss) prog ss
        (values,names,retCode,l1,l2) values (names,retCode,l1,l2) names (retCode,l1,l2)
        retCode (l1,l2) l1 l2 envs
        ⟨get,bad,find,rfl,rfl,rfl,rfl,rfl,rfl,rfl,valid,cut,clock⟩
  | some descriptor =>
    rcases descriptor with ⟨handlerVar,handlerCode,h1,h2⟩
    exact compCorrectCallReturningHandler ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source
      (inductionHypothesesOfOriginal ac values names retCode l1 l2 dest args
        handlerVar h1 h2 handlerCode source ⟨ih.1,ih.2.1,ih.2.2.1⟩)

theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (ih : OriginalInductionHypotheses ac ret dest args handler source) :
    SimulationB ac (.call ret dest args handler) source
      (sourceCost (.call ret dest args handler) source) := by
  cases ret with
  | none =>
    intro k f frame sourcePost target result bs bsPost n nPost compiled lens facts
    apply compCorrectCallTail ac dest args handler source ?_ k f frame sourcePost target
      result bs bsPost n nPost compiled lens facts
    intro xs args1 prog ss guards
    obtain ⟨get,bad,find,noHandler,clock⟩ := guards
    exact ih.2.2.2 xs (args1,prog,ss) args1 (prog,ss) prog ss
      ⟨get,bad,find,rfl,rfl,rfl,noHandler,clock⟩
  | some descriptor =>
    rcases descriptor with ⟨values,names,retCode,l1,l2⟩
    exact returningCallCase ac values names retCode l1 l2 dest args handler source ih



end InitECandidate.Solver.Wave8Stage.WordToStackCostCalls
