import InitECandidate.Solver.Wave8Stage.WordToStackTailClock
import InitECandidate.Solver.Wave8Stage.WordToStackReturnClock
import InitECandidate.Solver.Wave8Stage.WordToStackHandlerClock

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
Bounded Call constructor for arbitrary return and handler options. The four
literal source induction hypotheses retain every original guard. Tail calls
preserve the callee budget; returning calls add the applicable continuation
budget, using the maximum when both continuation forms are present.
-/

namespace InitECandidate.Solver.Wave8Stage.WordToStackCallClock
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open InitECandidate.Solver.Wave8Stage.WordToStackBounded


/-- Continuation alternatives are exclusive, so their budgets combine by maximum. -/
def callBudget {width : Nat}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (bodyBudget returnBudget handlerBudget : Nat) : Nat :=
  match ret with
  | none => bodyBudget
  | some _ => bodyBudget + match handler with
    | none => returnBudget
    | some _ => max returnBudget handlerBudget

def OriginalInductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (bodyBudget returnBudget handlerBudget : Nat) : Prop :=
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs v5 s2 v8 x ys s1,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 ∧
        WordSemStateFiniteExact.evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) = (v5, s2) ∧
        v5 = some v8 ∧ v8 = .result x ys ∧ ¬ (x ≠ .loc originalL1 originalL2 ∨ ys.length ≠ n.length) ∧
        WordSemStateFiniteExact.popEnv s2 = some s1 ∧ sptDomainEqUnion s1.locals envs.1 envs.2 →
      SimulationB ac retHandler (WordSemStateFiniteExact.setVars n ys s1) returnBudget) ∧
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
      SimulationB ac h (WordSemStateFiniteExact.setVar n' y s2) handlerBudget) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ ret = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      SimulationB ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs handler (WordSemStateFiniteExact.decClock source))) bodyBudget) ∧
    (∀ xs v3 args1 v10 prog ss,
      WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
      wordSemFindCode dest (wordSemAddRetLoc ret xs) source.code source.stackSize = some v3 ∧
      v3 = (args1,v10) ∧ v10 = (prog,ss) ∧ ret = none ∧ handler = none ∧ source.clock ≠ 0 →
      SimulationB ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.decClock source)) bodyBudget)

theorem inductionHypothesesOfOriginal {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    {bodyBudget returnBudget handlerBudget : Nat}
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
      SimulationB ac retHandler (WordSemStateFiniteExact.setVars n ys s1) returnBudget) ∧
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
      SimulationB ac h (WordSemStateFiniteExact.setVar n' y s2) handlerBudget) ∧
    (∀ xs v3 args1 v10 prog ss v1 n v6 originalNames v9 retHandler v11 originalL1 originalL2 envs,
        WordSemStateFiniteExact.getVars args source = some xs ∧ ¬ wordSemBadDestArgs dest args = true ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) source.code source.stackSize = some v3 ∧
        v3 = (args1, v10) ∧ v10 = (prog, ss) ∧ (some (values,names,retCode,l1,l2)) = some v1 ∧ v1 = (n, v6) ∧ v6 = (originalNames, v9) ∧
        v9 = (retHandler, v11) ∧ v11 = (originalL1, originalL2) ∧ ¬ (sptDomainEmpty originalNames.1 ∨ ¬ n.Nodup) ∧
        wordSemCutEnvs originalNames source.locals = some envs ∧ source.clock ≠ 0 →
      SimulationB ac prog (WordSemStateFiniteExact.callEnv args1 ss (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) bodyBudget)) :
    WordToStackHandlerClock.InductionHypotheses ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode
      source bodyBudget returnBudget handlerBudget := by
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
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : OriginalInductionHypotheses ac (some (values,names,retCode,l1,l2)) dest args handler source
      bodyBudget returnBudget handlerBudget) :
    SimulationB ac (.call (some (values,names,retCode,l1,l2)) dest args handler) source
      (callBudget (some (values,names,retCode,l1,l2)) handler bodyBudget returnBudget handlerBudget) := by
  cases handler with
  | none =>
    apply WordToStackReturnClock.compCorrectCallReturningNone ac values names retCode l1 l2 dest args source
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
    exact WordToStackHandlerClock.compCorrectCallReturningHandler ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source
      (inductionHypothesesOfOriginal ac values names retCode l1 l2 dest args
        handlerVar h1 h2 handlerCode source ⟨ih.1,ih.2.1,ih.2.2.1⟩)

theorem compCorrectCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width)
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : OriginalInductionHypotheses ac ret dest args handler source bodyBudget returnBudget handlerBudget) :
    SimulationB ac (.call ret dest args handler) source
      (callBudget ret handler bodyBudget returnBudget handlerBudget) := by
  cases ret with
  | none =>
    intro k f frame sourcePost target result bs bsPost n nPost compiled lens facts
    apply WordToStackTailClock.compCorrectCallTail ac dest args handler source bodyBudget ?_ k f frame sourcePost target
      result bs bsPost n nPost compiled lens facts
    intro xs args1 prog ss guards
    obtain ⟨get,bad,find,noHandler,clock⟩ := guards
    exact ih.2.2.2 xs (args1,prog,ss) args1 (prog,ss) prog ss
      ⟨get,bad,find,rfl,rfl,rfl,noHandler,clock⟩
  | some descriptor =>
    rcases descriptor with ⟨values,names,retCode,l1,l2⟩
    exact returningCallCase ac values names retCode l1 l2 dest args handler source ih

#print axioms compCorrectCall

end InitECandidate.Solver.Wave8Stage.WordToStackCallClock
