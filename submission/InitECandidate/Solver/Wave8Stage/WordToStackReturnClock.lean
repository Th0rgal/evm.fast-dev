import InitECandidate.Solver.Wave8Stage.WordToStackBounded
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturning.Execution

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
Quantitative returning calls without an exception handler. Adapted from the
pinned Flapjack CallReturning proof. The callee and continuation witnesses
carry separate bounds; the full constructor adds those bounds while retaining
source guards, caller restoration, metadata growth, and all resource exits.
-/

namespace InitECandidate.Solver.Wave8Stage.WordToStackReturnClock
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturning
open InitECandidate.Solver.Wave8Stage.WordToStackBounded


def InductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (bodyBudget returnBudget : Nat) : Prop :=
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (ys : List (WordLocW width))
    (calleePost popped : WordSemStateFiniteExact width (Nat × C) F),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 ∧
    WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location ys), calleePost) ∧
    ¬ (location ≠ .loc l1 l2 ∨ ys.length ≠ values.length) ∧
    WordSemStateFiniteExact.popEnv calleePost = some popped ∧
    sptDomainEqUnion popped.locals envs.1 envs.2 →
    SimulationB ac retCode (WordSemStateFiniteExact.setVars values ys popped) returnBudget) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    SimulationB ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none
          (WordSemStateFiniteExact.decClock source))) bodyBudget)

theorem simulateCalleeBodyAt {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize callerFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (saved : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (destinationCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize callerFrame source saved lens 0)
    (pushedRelation : stateRel ac k 0 0
      {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
      saved (callerFrame :: lens) 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * callerFrame + 2 * k)
    (destinationCompile : callDestNative dest args (k, callerSize, callerFrame) =
      (destinationCode, destination))
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (location calleeSize calleeFrame : Nat) (body : HolProg width)
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (targetCode : sptLookup location saved.code = some
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body))
    (bodyCompile : compNative ac false prog (bs, n) (k, calleeSize, calleeFrame) =
      (body, (bsPost, nPost)))
    (bodyConventions : postAllocConventionsHOL k prog = true)
    (bodyFlat : flatExpConventions prog = true)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ saved.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (saved.bitmaps.drop (n - (appListAppend bs).length)))
    (calleeLocalsSize : ss.getD calleeSize = calleeSize)
    (calleeShape : if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1)
    (argumentBound : args1.length - k ≤ calleeFrame)
    (bodyMaximum : maxVarHOL prog < 2 * calleeFrame + 2 * k)
    (space : calleeSize ≤ saved.stackSpace) :
    ∃ (moved entry : StackSemStateFiniteExact width C F)
          (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1)
            (k, callerSize, callerFrame), saved) = (none, moved) ∧
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none
                (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (callerFrame :: lens) ∧
      extraClock ≤ bodyBudget := by
  obtain ⟨moved, entry, moveRun, allocationRun, entryRelation⟩ :=
    enterCallee ac k callerSize callerFrame calleeSize calleeFrame values names retCode
      l1 l2 dest args source saved lens xs args1 prog ss envs destinationCode destination
      guards callerRelation pushedRelation conventions maximum destinationCompile
      calleeShape calleeLocalsSize argumentBound space
  have moveGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackArgsNative destination (args.length + 1) (k, callerSize, callerFrame))
    saved moved none moveRun
  have entryGrowth := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize - (args1.length - k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved))
    entry none allocationRun
  have bitmapGrowth : saved.bitmaps.IsPrefix entry.bitmaps :=
    moveGrowth.1.trans entryGrowth.1
  have codeGrowth : sptSubspt saved.code entry.code :=
    sptSubsptTrans _ _ _ ⟨moveGrowth.2, entryGrowth.2⟩
  have labels : ∀ loc, StackSem.getLabelsExact body loc →
      StackSem.locCheckExact entry.code loc := by
    intro loc member
    apply LocationLabels.locCheckSubset saved.code entry.code codeGrowth loc
    exact Or.inr ⟨location, .seq (.stackAlloc (calleeSize - (args1.length - k))) body,
      targetCode, by unfold StackSem.getLabelsExact; exact Or.inr member⟩
  have bodyNotError := calleeNotError values names retCode l1 l2 dest args source
    sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution
    notError bodyRun
  obtain ⟨extraClock, clockBound, targetPost, targetResult, targetRun, conclusion⟩ :=
    ih.2 xs args1 prog ss envs ⟨guards, nonzero⟩ k calleeSize calleeFrame bodyPost entry
      bodyResult bs bsPost n nPost body (callerFrame :: lens)
      ⟨bodyRun, bodyNotError, entryRelation, bodyConventions, bodyFlat, bodyCompile,
        bitmapLength, bitmapBound.trans bitmapGrowth.length_le,
        bitmapPrefix.trans (bitmapGrowth.drop _), labels, bodyMaximum⟩
  have allocationClock : ∀ extra : Nat,
      StackSemEvaluate.evaluate
        (.stackAlloc (calleeSize - (args1.length - k)),
          {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
            clock := (StackSemStateOps.decClock moved).clock + extra}) =
        (none, {entry with clock := entry.clock + extra}) := by
    intro extra
    have success := allocationRun
    rw [StackSemEvaluate.evaluate_stackAlloc] at success
    split_ifs at success with disabled insufficient
    · cases (Prod.mk.inj success).1
    · cases (Prod.mk.inj success).1
    obtain ⟨_, rfl⟩ := Prod.mk.inj success
    rw [StackSemEvaluate.evaluate_stackAlloc, if_neg disabled, if_neg insufficient]
    rfl
  have calleeRun : StackSemEvaluate.evaluate
      (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
          clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
      (targetResult, targetPost) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      allocationClock extraClock]
    exact targetRun
  exact ⟨moved, entry, extraClock, targetPost, targetResult, moveRun, allocationRun,
    targetRun, calleeRun, conclusion, clockBound⟩

theorem simulatePreparedCalleeBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (space : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤ target.stackSpace) :
    ∃ (destinationTarget saved moved : StackSemStateFiniteExact width C F)
      (location calleeSize calleeFrame : Nat) (body : HolProg width)
      (calleeBs calleeBsPost : AppList (BitVec width)) (calleeIndex calleeIndexPost : Nat),
      StackSemEvaluate.evaluate (destinationCode, target) = (none, destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode, destinationTarget) = (none, saved) ∧
      StackSemEvaluate.evaluate (stackArgsNative destination (args.length + 1) (k, f, frame), saved) =
        (none, moved) ∧
      stateRel ac k f frame source saved lens 0 ∧
      stateRel ac k 0 0
        {WordSemStateFiniteExact.pushEnv envs none source with locals := .ln, localsSize := some 0}
        saved (frame :: lens) 0 ∧
      sptLookup location source.code = some (args1.length, prog) ∧
      sptLookup location saved.code = some
        (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      compNative ac false prog (calleeBs, calleeIndex) (k, calleeSize, calleeFrame) =
        (body, (calleeBsPost, calleeIndexPost)) ∧
      postAllocConventionsHOL k prog = true ∧ flatExpConventions prog = true ∧
      (appListAppend calleeBs).length ≤ calleeIndex ∧
      calleeIndex - (appListAppend calleeBs).length ≤ target.bitmaps.length ∧
      (appListAppend calleeBsPost).IsPrefix
        (target.bitmaps.drop (calleeIndex - (appListAppend calleeBs).length)) ∧
      ss.getD calleeSize = calleeSize ∧
      (if calleeFrame = 0 then calleeSize = 0 else calleeSize = calleeFrame + 1) ∧
      args1.length - k ≤ calleeFrame ∧ maxVarHOL prog < 2 * calleeFrame + 2 * k ∧
      calleeFrame = max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code =
        some (.seq (.stackAlloc (calleeSize - (args1.length - k))) body) ∧
      saved.stackSpace = target.stackSpace ∧
      (calleeSize ≤ target.stackSpace →
        ∃ (entry : StackSemStateFiniteExact width C F) (extraClock : Nat)
          (targetPost : StackSemStateFiniteExact width C F)
          (targetResult : Option (StackSemResult width)),
          StackSemEvaluate.evaluate
            (.stackAlloc (calleeSize - (args1.length - k)),
              StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
            (none, entry) ∧
          StackSemEvaluate.evaluate (body, {entry with clock := entry.clock + extraClock}) =
            (targetResult, targetPost) ∧
          StackSemEvaluate.evaluate
            (.seq (.stackAlloc (calleeSize - (args1.length - k))) body,
              {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
                clock := (StackSemStateOps.decClock moved).clock + extraClock}) =
            (targetResult, targetPost) ∧
          compCorrectResult ac k calleeSize calleeFrame
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
            bodyPost targetPost bodyResult targetResult (frame :: lens) ∧
          extraClock ≤ bodyBudget) := by
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, movedState⟩ :=
    prepareCalleeDestinationAt ac k f frame values names retCode l1 l2 dest args source target
      lens xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      bitmapPrefix space
  refine ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, moveRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, ?_⟩
  intro calleeSpace
  have destinationGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun).1
  have savedGrowth := (Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun).1
  have bitmapGrowth : target.bitmaps.IsPrefix saved.bitmaps :=
    destinationGrowth.trans savedGrowth
  obtain ⟨movedAgain, entry, extraClock, targetPost, targetResult, moveAgain,
    allocationRun, targetRun, calleeRun, conclusion, clockBound⟩ :=
    simulateCalleeBodyAt ac k f frame values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult saved lens xs args1 prog ss envs destinationCode destination
      guards savedRelation pushedRelation conventions maximum destinationCompile ih nonzero
      execution notError bodyRun location calleeSize calleeFrame body calleeBs calleeBsPost
      calleeIndex calleeIndexPost savedLookup bodyCompile bodyConventions bodyFlat
      calleeBitmapLength (calleeBitmapBound.trans bitmapGrowth.length_le)
      (calleeBitmapPrefix.trans (bitmapGrowth.drop _)) calleeLocalsSize calleeShape
      calleeArgumentBound bodyMaximum (by rwa [savedSpace])
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans moveRun)
  subst movedAgain
  exact ⟨entry, extraClock, targetPost, targetResult, allocationRun, targetRun, calleeRun,
    conclusion, clockBound⟩

theorem sourceReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost)) :
    ∃ (gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
      (popped : WordSemStateFiniteExact width (Nat × C) F),
      bodyPost.stack = .stackFrame source.localsSize (sptToAList envs.1) gc none :: tail ∧
      ((wordSemEnvToList envs.2 source.permute).1).map Prod.fst = gc.map Prod.fst ∧
      WordSemStackEq.sKeyEq source.stack tail ∧ bodyPost.handler = source.handler ∧
      popped = {bodyPost with
        locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
        stack := tail, localsSize := source.localsSize} ∧
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      sptDomainEqUnion popped.locals envs.1 envs.2 ∧
      ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      SimulationB ac retCode (WordSemStateFiniteExact.setVars values returned popped) returnBudget := by
  obtain ⟨gc, tail, frame, gcKeys, tailKeys, handler, popRun, domain⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  let popped : WordSemStateFiniteExact width (Nat × C) F := {bodyPost with
    locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
    stack := tail, localsSize := source.localsSize}
  have originalGuards := guards
  obtain ⟨get, bad, find, valid, cut⟩ := originalGuards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get, bad, Bool.false_eq_true, if_false, find, valid, cut] at execution
  rw [dif_neg nonzero, WordSemStateFiniteExact.fix_clock_evaluate, bodyRun] at execution
  simp only at execution
  by_cases invalid : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
  · rw [if_pos invalid] at execution
    exact False.elim (notError (Prod.mk.inj execution).1.symm)
  rw [if_neg invalid, popRun] at execution
  simp only at execution
  rw [if_pos domain] at execution
  refine ⟨gc, tail, popped, frame, gcKeys, tailKeys, handler, rfl, popRun, domain,
    invalid, execution, ?_⟩
  exact ih.1 xs args1 prog ss envs location returned bodyPost popped
    ⟨guards, nonzero, bodyRun, invalid, popRun, domain⟩

theorem restoreCallerFromBodyReturn {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      SimulationB ac retCode (WordSemStateFiniteExact.setVars values returned popped) returnBudget ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      stateRel ac k callerSize frame
        (WordSemStateFiniteExact.setVars values returned popped) restored lens 0 := by
  obtain ⟨gc, tail, popped, sourceFrame, _, _, _, popShape, popRun, domain,
    valid, continuationRun, continuationIH⟩ :=
    sourceReturningContinuation ac values names retCode l1 l2 dest args source sourcePost
      bodyPost result xs args1 prog ss envs location returned guards ih nonzero execution
      notError bodyRun
  have kBound : 4 < k := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  obtain ⟨positive, canonical, nameBound, physical⟩ :=
    returningCallerLocalObligations k frame values names retCode l1 l2 dest args source
      xs args1 prog ss envs popped.locals guards conventions maximum (by omega) domain
  have callerShape : if frame = 0 then callerSize = 0 else callerSize = frame + 1 := by
    have h := callerRelation
    unfold stateRel at h
    aesop (config := { enableSimp := false })
  have callerSizeEq : callerSize = frame + 1 := by
    rw [if_neg (by omega)] at callerShape
    exact callerShape
  have lengthEq := (not_or.mp valid).2
  have countEq : returned.length - (k - 1) =
      Compiler.Backend.WordToStack.numStackRet k values := by
    unfold Compiler.Backend.WordToStack.numStackRet
    omega
  simp only [compCorrectResult, Option.map_some, compileResult, ne_eq,
    not_true_eq_false, ↓reduceIte] at bodyConclusion
  obtain ⟨bodyRelation, placements⟩ := bodyConclusion
  rw [countEq] at bodyRelation
  subst popped
  obtain ⟨restored, copyRun, restoredRelation⟩ :=
    copyReturnRestoresCallerState ac k frame bodyPost target source.localsSize
      (sptToAList envs.1) gc tail lens values returned (by omega) canonical
      (by omega) (by omega) physical sourceFrame bodyRelation placements
  refine ⟨_, restored, popRun, continuationRun, continuationIH, ?_, ?_⟩
  · rwa [callerSizeEq]
  · rw [callerSizeEq]
    exact restoredRelation

theorem executeReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat) (values : List Nat)
    (retCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (target restored : StackSemStateFiniteExact width C F)
    (result : Option (WordSemResult width))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat)
    (compiled : HolProg width) (lens : List Nat)
    {budget : Nat}
    (ih : SimulationB ac retCode source budget)
    (sourceRun : WordSemStateFiniteExact.evaluate retCode source = (result, sourcePost))
    (notError : result ≠ some .error)
    (related : stateRel ac k f frame source restored lens 0)
    (conventions : postAllocConventionsHOL k retCode = true)
    (flat : flatExpConventions retCode = true)
    (compilation : compNative ac false retCode (bs, n) (k, f, frame) = (compiled, (bsPost, nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ restored.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix
      (restored.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact restored.code loc)
    (maximum : maxVarHOL retCode < 2 * frame + 2 * k)
    (copyRun : StackSemEvaluate.evaluate
      (copyRetNative false false (k, f, frame) values .skip, target) = (none, restored)) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, f, frame) values compiled,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k f frame source sourcePost targetPost result targetResult lens ∧
      extraClock ≤ budget := by
  obtain ⟨extraClock, clockBound, targetPost, targetResult, continuationRun, conclusion⟩ :=
    ih k f frame sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceRun, notError, related, conventions, flat, compilation, lengthBound,
        bitmapBound, bitmapPrefix, labels, maximum⟩
  have clockFree := returnCopyClockFree (width := width) (C := C) (F := F) k f frame values
  have sameClock := clockFree target target.clock
  rw [show {target with clock := target.clock} = target from rfl, copyRun] at sameClock
  simp only [Prod.map, id_eq, Prod.mk.injEq] at sameClock
  have clockEq : restored.clock = target.clock := by
    have projected := congrArg
      (fun state : StackSemStateFiniteExact width C F => state.clock) sameClock.2
    exact projected
  have clockedCopy := clockFree target (target.clock + extraClock)
  rw [copyRun] at clockedCopy
  simp only [Prod.map, id_eq] at clockedCopy
  have outputClock : {restored with clock := target.clock + extraClock} =
      {restored with clock := restored.clock + extraClock} := by rw [clockEq]
  rw [outputClock] at clockedCopy
  refine ⟨extraClock, targetPost, targetResult, ?_, conclusion, clockBound⟩
  rw [CallReturnEval.evaluateCopyRetSeq, StackSemEvaluate.evaluate_seq,
    StackSemEvaluateClock.fixClockEvaluate, clockedCopy]
  simp only
  exact continuationRun

theorem simulateReturningContinuationFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target)) :
    ∃ (popped : WordSemStateFiniteExact width (Nat × C) F)
      (restored : StackSemStateFiniteExact width C F)
      (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values .skip, target) = (none, restored) ∧
      StackSemEvaluate.evaluate
        (copyRetNative false false (k, callerSize, frame) values returnCode,
          {target with clock := target.clock + extraClock}) = (targetResult, targetPost) ∧
      compCorrectResult ac k callerSize frame source sourcePost targetPost result targetResult lens ∧
      extraClock ≤ returnBudget := by
  obtain ⟨popped, restored, popRun, sourceContinuation, continuationIH, copyRun, restoredRelation⟩ :=
    restoreCallerFromBodyReturn ac k callerSize frame calleeSize calleeFrame values names
      retCode l1 l2 dest args source sourcePost bodyPost result location returned saved target
      lens xs args1 prog ss envs guards callerRelation conventions maximum ih nonzero
      execution notError bodyRun bodyConclusion
  obtain ⟨retConventions, retFlat, retMaximum, retLength, retBitmapBound, retBitmapPrefix, retLabels⟩ :=
    continuationCompilationFacts ac k callerSize frame values names retCode l1 l2 dest args
      initial bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode
      returnCode compiled destination conventions flat maximum destinationCompile savedCompile
      returnCompile compilation lengthBound bitmapBound bitmapPrefix labels
  obtain ⟨bitmapGrowth, codeGrowth⟩ := returningHistoryGrowth initial saved moved target restored
    (.seq destinationCode savedCode)
    (stackArgsNative destination (args.length + 1) (k, callerSize, frame)) callee
    k callerSize frame l1 l2 bodyExtraClock values (some (.result location))
    preludeRun argumentsRun calleeRun copyRun
  have restoredLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset initial.code restored.code codeGrowth loc (retLabels loc member)
  obtain ⟨extraClock, targetPost, targetResult, targetContinuation, conclusion, clockBound⟩ :=
    executeReturningContinuation ac k callerSize frame values retCode
      (WordSemStateFiniteExact.setVars values returned popped) sourcePost target restored result
      savedBitmaps finalBitmaps savedIndex finalIndex returnCode lens continuationIH
      sourceContinuation notError restoredRelation retConventions retFlat returnCompile retLength
      (retBitmapBound.trans bitmapGrowth.length_le)
      (retBitmapPrefix.trans (bitmapGrowth.drop _)) restoredLabels retMaximum copyRun
  obtain ⟨gc, tail, sourceFrame, _, _, sourceHandler, _, _⟩ :=
    returnedCallerFrame prog source bodyPost envs args1 ss location returned bodyRun
  have poppedHandler : popped.handler = bodyPost.handler := by
    have pop := popRun
    rw [WordSemStateFiniteExact.popEnv, sourceFrame] at pop
    have shape := Option.some.inj pop
    rw [← shape]
  have handler : (WordSemStateFiniteExact.setVars values returned popped).handler = source.handler :=
    poppedHandler.trans sourceHandler
  rw [returningResultInitialHandler ac k callerSize frame source
    (WordSemStateFiniteExact.setVars values returned popped) sourcePost targetPost
    result targetResult lens handler] at conclusion
  exact ⟨popped, restored, extraClock, targetPost, targetResult, popRun, copyRun,
    targetContinuation, conclusion, clockBound⟩

theorem normalCompiledCallFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k callerSize frame calleeSize calleeFrame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (saved target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (callerRelation : stateRel ac k callerSize frame source saved lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost))
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source)))
      bodyPost target (some (.result location returned)) (some (.result location)) (frame :: lens))
    (initial moved : StackSemStateFiniteExact width C F)
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled callee : HolProg width)
    (destination : Sum Nat Nat) (bodyExtraClock : Nat)
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (destinationCompile : callDestNative dest args (k, callerSize, frame) =
      (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, callerSize, frame) =
      (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, callerSize, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, callerSize, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ initial.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (initial.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact initial.code loc)
    (preludeRun : StackSemEvaluate.evaluate (.seq destinationCode savedCode, initial) = (none, saved))
    (argumentsRun : StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) = (none, moved))
    (calleeRun : StackSemEvaluate.evaluate
      (callee, {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock + bodyExtraClock}) =
      (some (.result location), target))
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some callee) :
    ∃ (extraClock : Nat) (targetPost : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {initial with clock := initial.clock + extraClock}) =
        (targetResult, targetPost) ∧
      compCorrectResult ac k callerSize frame source sourcePost targetPost result targetResult lens ∧
      extraClock ≤ bodyExtraClock + returnBudget := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, valid, _, _⟩ := sourceReturningContinuation ac values names
    retCode l1 l2 dest args source sourcePost bodyPost result xs args1 prog ss envs location
    returned guards ih nonzero execution notError bodyRun
  have locationEq : location = .loc l1 l2 := by
    by_contra different
    exact valid (Or.inl different)
  obtain ⟨popped, restored, continuationClock, finalTarget, finalResult, _, _, continuationRun,
    conclusion, clockBound⟩ := simulateReturningContinuationFromHistory ac k callerSize frame calleeSize
    calleeFrame values names retCode l1 l2 dest args source sourcePost bodyPost result location
    returned saved target lens xs args1 prog ss envs guards callerRelation conventions maximum
    ih nonzero execution notError bodyRun bodyConclusion initial moved bs savedBitmaps finalBitmaps
    n savedIndex finalIndex destinationCode savedCode returnCode compiled callee destination
    bodyExtraClock flat destinationCompile savedCompile returnCompile compilation lengthBound
    bitmapBound bitmapPrefix labels preludeRun argumentsRun calleeRun
  have argumentClock := stackArgumentsClockFree (C := C) (F := F) k callerSize frame
    destination (args.length + 1) saved saved.clock
  change StackSemEvaluate.evaluate
      (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved) =
    Prod.map id (fun state => {state with clock := saved.clock})
      (StackSemEvaluate.evaluate
        (stackArgsNative destination (args.length + 1) (k, callerSize, frame), saved)) at argumentClock
  rw [argumentsRun] at argumentClock
  have movedClock : moved.clock = saved.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj argumentClock).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [movedClock, ← callerRelation.1]
    exact nonzero
  have actualContinuation : StackSemEvaluate.evaluate
      (.seq .skip (copyRetNative false false (k, callerSize, frame) values returnCode),
        {target with clock := target.clock + continuationClock}) = (finalResult, finalTarget) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate,
      StackSemEvaluate.evaluate_skip]
    exact continuationRun
  rw [locationEq] at calleeRun
  have callRun := returningCallContinuationRun moved target finalTarget l1 l2 bodyExtraClock
    continuationClock destination callee
    (.seq .skip (copyRetNative false false (k, callerSize, frame) values returnCode)) finalResult
    found movedNonzero calleeRun actualContinuation
  have completePrelude : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode
        (stackArgsNative destination (args.length + 1) (k, callerSize, frame))), initial) =
      (none, moved) := by
    rw [Compiler.Backend.StackRemove.CopyLoopProof.sequenceAssoc,
      StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, preludeRun]
    exact argumentsRun
  refine ⟨bodyExtraClock + continuationClock, finalTarget, finalResult, ?_, conclusion, by omega⟩
  exact completeCallFromPrelude ac k callerSize frame values names retCode l1 l2 dest args
    bs savedBitmaps finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled
    destination initial moved finalTarget (bodyExtraClock + continuationClock) finalResult
    destinationCompile savedCompile returnCompile compilation completePrelude callRun

theorem simulateSuccessfulCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps finalBitmaps : AppList (BitVec width)) (n savedIndex finalIndex : Nat)
    (destinationCode savedCode returnCode compiled : HolProg width) (destination : Sum Nat Nat)
    (guards : SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args none) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) =
      (returnCode, (finalBitmaps, finalIndex)))
    (compilation : compNative ac false
      (.call (some (values, names, retCode, l1, l2)) dest args none) (bs, n) (k, f, frame) =
      (compiled, (finalBitmaps, finalIndex)))
    (flat : flatExpConventions
      (.call (some (values, names, retCode, l1, l2)) dest args none) = true)
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend finalBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args none) source =
      (result, sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) =
      (bodyResult, bodyPost))
    (space : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace) :
    ∃ (extra : Nat) (targetFinal : StackSemStateFiniteExact width C F)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extra}) =
        (targetResult, targetFinal) ∧
      compCorrectResult ac k f frame source sourcePost targetFinal result targetResult lens ∧
      extra ≤ bodyBudget + returnBudget := by
  let expectedFrame := max (maxVarHOL prog / 2 + 1 - k) (args1.length - k)
  have countEq := stackArgumentCount values names retCode l1 l2 dest args source xs args1
    prog ss envs k f frame destinationCode destination guards destinationCompile
  have argumentsSpace : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace := by
    rw [countEq]
    have bound : args1.length - k ≤ expectedFrame := Nat.le_max_right _ _
    change (if expectedFrame = 0 then 0 else expectedFrame + 1) ≤ _ at space
    split_ifs at space <;> omega
  have savedPrefix := (compImpIsPrefix ac false retCode (savedBitmaps, savedIndex) (k, f, frame)
    returnCode (finalBitmaps, finalIndex) returnCompile).trans bitmapPrefix
  obtain ⟨destinationTarget, saved, moved, location, calleeSize, calleeFrame, body,
    calleeBs, calleeBsPost, calleeIndex, calleeIndexPost, destinationRun, savedRun, argumentsRun,
    savedRelation, pushedRelation, sourceCode, savedLookup, bodyCompile, bodyConventions,
    bodyFlat, calleeBitmapLength, calleeBitmapBound, calleeBitmapPrefix, calleeLocalsSize,
    calleeShape, calleeArgumentBound, bodyMaximum, calleeFrameEq, found, savedSpace, simulation⟩ :=
    simulatePreparedCalleeBody ac k f frame values names retCode l1 l2 dest args source target lens
      xs args1 prog ss envs bs savedBitmaps n savedIndex destinationCode savedCode destination
      guards related conventions maximum destinationCompile savedCompile bitmapLength bitmapBound
      savedPrefix sourcePost bodyPost result bodyResult ih nonzero execution notError bodyRun argumentsSpace
  have calleeSpace : calleeSize ≤ target.stackSpace := by
    change calleeFrame = expectedFrame at calleeFrameEq
    change (if expectedFrame = 0 then 0 else expectedFrame + 1) ≤ _ at space
    rw [calleeFrameEq] at calleeShape
    split_ifs at calleeShape space <;> omega
  obtain ⟨entry, bodyExtra, calleeTarget, targetResult, allocationRun, bodyTargetRun,
    calleeRun, bodyConclusion, bodyClockBound⟩ := simulation calleeSpace
  have savedPrelude : StackSemEvaluate.evaluate (.seq destinationCode savedCode, target) =
      (none, saved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    exact savedRun
  have preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode
        (stackArgsNative destination (args.length + 1) (k, f, frame))), target) = (none, moved) := by
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq, StackSemEvaluateClock.fixClockEvaluate, savedRun]
    exact argumentsRun
  have free := completePreludeClockFree (C := C) (F := F) k f frame dest args names
    (bs, n) (savedBitmaps, savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free target target.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode
      (stackArgsNative destination (args.length + 1) (k, f, frame))), target) =
    (Prod.map id (fun state => {state with clock := target.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode
          (stackArgsNative destination (args.length + 1) (k, f, frame))), target)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = target.clock := congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by rw [clockEq, ← related.1]; exact nonzero
  let callee : HolProg width := .seq (.stackAlloc (calleeSize - (args1.length - k))) body
  let continuation : HolProg width := .seq .skip (copyRetNative false false (k, f, frame) values returnCode)
  have finishTerminal
      (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
        ∃ event, targetResult = some (.finalFFI event)) :
      ∃ extra targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled, {target with clock := target.clock + extra}) =
          (finalResult, targetFinal) ∧
        compCorrectResult ac k f frame source sourcePost targetFinal result finalResult lens ∧
        extra ≤ bodyBudget + returnBudget := by
    obtain ⟨callRun, conclusion⟩ := terminalCallFromCallee ac k f frame calleeSize calleeFrame values
      names retCode l1 l2 dest args source sourcePost bodyPost result bodyResult target moved calleeTarget
      targetResult lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
      nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    exact ⟨bodyExtra, calleeTarget, targetResult,
      completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
        finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
        target moved calleeTarget bodyExtra targetResult destinationCompile savedCompile returnCompile
        compilation preludeRun callRun, conclusion, by omega⟩
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := calleeOutcomeCases values names retCode l1 l2 dest args source sourcePost
      bodyPost result bodyResult xs args1 prog ss envs guards nonzero execution bodyRun notError
    rcases outcomes with ⟨returnLocation, returned, rfl⟩ | ⟨exceptionLocation, value, rfl⟩ |
      timeout | resource | ⟨event, ffi⟩
    · have targetEq : targetResult = some (.result returnLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      obtain ⟨extraClock, targetPost, targetResult, run, conclusion, clockBound⟩ :=
        normalCompiledCallFromHistory ac k f frame calleeSize calleeFrame values names retCode
        l1 l2 dest args source sourcePost bodyPost result returnLocation returned saved calleeTarget lens
        xs args1 prog ss envs guards savedRelation conventions maximum ih nonzero execution notError
        bodyRun bodyConclusion target moved bs savedBitmaps finalBitmaps n savedIndex finalIndex
        destinationCode savedCode returnCode compiled callee destination bodyExtra flat destinationCompile
        savedCompile returnCompile compilation bitmapLength bitmapBound bitmapPrefix labels savedPrelude
        argumentsRun calleeRun found
      exact ⟨extraClock, targetPost, targetResult, run, conclusion, by omega⟩
    · have targetEq : targetResult = some (.exception exceptionLocation) := by
        simpa only [Option.map_some, compileResult] using matching.symm
      subst targetResult
      obtain ⟨callRun, conclusion⟩ := exceptionCallFromCallee ac k f frame calleeSize calleeFrame values
        names retCode l1 l2 dest args source sourcePost bodyPost result exceptionLocation value target moved
        calleeTarget lens xs args1 prog ss envs bodyExtra destination callee continuation guards related
        nonzero execution bodyRun found movedNonzero calleeRun bodyConclusion
      exact ⟨bodyExtra, calleeTarget, some (.exception exceptionLocation),
        completeCallFromPrelude ac k f frame values names retCode l1 l2 dest args bs savedBitmaps
          finalBitmaps n savedIndex finalIndex destinationCode savedCode returnCode compiled destination
          target moved calleeTarget bodyExtra (some (.exception exceptionLocation)) destinationCompile
          savedCompile returnCompile compilation preludeRun callRun, conclusion, by omega⟩
    · apply finishTerminal; left
      simpa only [timeout, Option.map_some, compileResult] using matching.symm
    · apply finishTerminal; right; left
      exact ⟨.word 1, by simpa only [resource, Option.map_some, compileResult] using matching.symm⟩
    · apply finishTerminal; right; right
      exact ⟨event, by simpa only [ffi, Option.map_some, compileResult] using matching.symm⟩
  · have mismatch := bodyConclusion
    unfold compCorrectResult at mismatch
    rw [if_pos matching] at mismatch
    exact finishTerminal (Or.inr (Or.inl ⟨.word 2, mismatch.1⟩))

theorem compCorrectCallReturningNone {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    {bodyBudget returnBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args source bodyBudget returnBudget) :
    SimulationB ac (.call (some (values, names, retCode, l1, l2)) dest args none) source
      (bodyBudget + returnBudget) := by
  intro k f frame sourcePost target result bs finalBitmaps n finalIndex compiled lens premises
  obtain ⟨execution, notError, related, conventions, flat, compilation, bitmapLength,
    bitmapBound, bitmapPrefix, labels, maximum⟩ := premises
  obtain ⟨xs, args1, prog, ss, envs, guards⟩ := sourceGuardsOfNotError values names retCode l1 l2
    dest args source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := width) dest args (k, f, frame) with ⟨destinationCode, destination⟩
  rcases savedCompile : wLiveNative names (bs, n) (k, f, frame) with
    ⟨savedCode, savedBitmaps, savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps, savedIndex) (k, f, frame) with
    ⟨returnCode, returnBitmaps, returnIndex⟩
  have shape := compilation
  simp only [compNative, destinationCompile, savedCompile, returnCompile,
    Bool.false_eq_true, if_false, Prod.mk.injEq] at shape
  obtain ⟨bitmapsEq, indexEq⟩ := shape.2
  subst finalBitmaps
  subst finalIndex
  by_cases argumentsSpace : Compiler.Backend.WordToStack.stackArgCount destination (args.length + 1) k ≤
      target.stackSpace
  · by_cases zero : source.clock = 0
    · obtain ⟨targetPost, run, conclusion⟩ := compiledCallTimeout ac k f frame values names retCode
        l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
        returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
        related conventions maximum destinationCompile savedCompile returnCompile bitmapLength
        bitmapBound compiled compilation execution argumentsSpace zero bitmapPrefix
      exact ⟨0, Nat.zero_le _, targetPost, some .timeOut, by simpa only [Nat.add_zero] using run, conclusion⟩
    · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) = 0 then 0
          else max (maxVarHOL prog / 2 + 1 - k) (args1.length - k) + 1) ≤ target.stackSpace
      · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
          (WordSemStateFiniteExact.callEnv args1 ss
            (WordSemStateFiniteExact.pushEnv envs none (WordSemStateFiniteExact.decClock source))) with
          ⟨bodyResult, bodyPost⟩
        obtain ⟨extra, targetFinal, targetResult, run, conclusion, clockBound⟩ :=
          simulateSuccessfulCall ac k f frame values names retCode l1 l2 dest args source target
          lens xs args1 prog ss envs bs savedBitmaps returnBitmaps n savedIndex returnIndex
          destinationCode savedCode returnCode compiled destination guards related conventions maximum
          destinationCompile savedCompile returnCompile compilation flat labels bitmapLength bitmapBound
          bitmapPrefix sourcePost bodyPost result bodyResult ih zero execution notError bodyRun calleeSpace
        exact ⟨extra, clockBound, targetFinal, targetResult, run, conclusion⟩
      · obtain ⟨calleeSize, _, sizeEq, failure⟩ := compiledCalleeFrameFailure ac k f frame values names
          retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
          returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards
          related conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound
          compiled compilation execution argumentsSpace zero bitmapPrefix
        obtain ⟨targetPost, run, conclusion⟩ := failure (by rw [sizeEq]; omega)
        exact ⟨0, Nat.zero_le _, targetPost, some (.halt (.word (BitVec.ofNat width 2))), by simpa only [Nat.add_zero] using run, conclusion⟩
  · obtain ⟨targetPost, run, conclusion⟩ := compiledStackArgumentsFailure ac k f frame values names
      retCode l1 l2 dest args source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps
      returnBitmaps n savedIndex returnIndex destinationCode savedCode returnCode destination guards related
      conventions maximum destinationCompile savedCompile returnCompile bitmapLength bitmapBound compiled
      compilation execution (by omega) bitmapPrefix
    exact ⟨0, Nat.zero_le _, targetPost, some (.halt (.word (BitVec.ofNat width 2))), by simpa only [Nat.add_zero] using run, conclusion⟩

#print axioms compCorrectCallReturningNone

end InitECandidate.Solver.Wave8Stage.WordToStackReturnClock
