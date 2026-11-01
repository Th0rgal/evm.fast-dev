import InitECandidate.Solver.Wave8Stage.WordToStackBounded
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.CallReturningHandler.Execution

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
Quantitative returning calls with an exception handler, adapted from the
pinned Flapjack CallReturningHandler proof. The full constructor uses the
callee budget plus the maximum of the normal and exceptional continuation
budgets. Original guarded source states, full caller restoration and every
timeout or resource exit are retained.
-/

namespace InitECandidate.Solver.Wave8Stage.WordToStackHandlerClock
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCorrect.CallReturningHandler
open Flapjack.WordToStackProofs.CallReturnHandler
open InitECandidate.Solver.Wave8Stage.WordToStackBounded


def InductionHypotheses {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (bodyBudget returnBudget handlerBudget : Nat) : Prop :=
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
    SimulationB ac retCode (WordSemStateFiniteExact.setVars values ys popped) returnBudget) ∧
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
    SimulationB ac handlerCode (WordSemStateFiniteExact.setVar handlerVar value calleePost) handlerBudget) ∧
  (∀ (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width)),
    CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs ∧
    source.clock ≠ 0 →
    SimulationB ac prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyBudget)

theorem simulateHandlerCalleeBody {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k f frame : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps : AppList (BitVec width)) (n savedIndex : Nat)
    (destinationCode savedCode : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k f frame source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * frame + 2 * k)
    (destinationCompile : callDestNative dest args (k, f, frame) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, f, frame) = (savedCode, (savedBitmaps, savedIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend savedBitmaps).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (room : 3 ≤ target.stackSpace)
    (location : StackSem.locCheckExact target.code (h1,h2))
    (space : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3)
    (nonzero : source.clock ≠ 0)
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) = (bodyResult,bodyPost))
    {bodyBudget returnBudget handlerBudget : Nat}
    (hypotheses : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget) :
    ∃ (destinationTarget saved header moved entry targetPost : StackSemStateFiniteExact width C F)
      (calleeCode body : HolProg width) (calleeSize calleeFrame extra : Nat)
      (targetResult : Option (StackSemResult width)),
      StackSemEvaluate.evaluate (destinationCode,target) = (none,destinationTarget) ∧
      StackSemEvaluate.evaluate (savedCode,destinationTarget) = (none,saved) ∧
      StackSemEvaluate.evaluate (pushHandlerNative false h1 h2 (k,f,frame),saved) = (none,header) ∧
      StackSemEvaluate.evaluate
        (stackHandlerArgsNative false destination (args.length+1) (k,f,frame),header) =
          (none,moved) ∧
      StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode ∧
      calleeCode = .seq (.stackAlloc (calleeSize-(args1.length-k))) body ∧
      StackSemEvaluate.evaluate (.stackAlloc (calleeSize-(args1.length-k)),
        StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) =
          (none,entry) ∧
      StackSemEvaluate.evaluate (body,{entry with clock := entry.clock+extra}) =
        (targetResult,targetPost) ∧
      StackSemEvaluate.evaluate
        (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
          with clock := (StackSemStateOps.decClock moved).clock + extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k calleeSize calleeFrame
        (WordSemStateFiniteExact.callEnv args1 ss
          (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
            (WordSemStateFiniteExact.decClock source))) bodyPost targetPost bodyResult
        targetResult (frame :: lens) ∧
      extra ≤ bodyBudget := by
  let expectedFrame := max (maxVarHOL prog / 2 + 1-k) (args1.length-k)
  have countEq := CallReturning.stackArgumentCount values names retCode l1 l2 dest args
    source xs args1 prog ss envs k f frame destinationCode destination guards destinationCompile
  have countBound : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
      target.stackSpace-3 := by
    rw [countEq]
    have capacity : args1.length-k ≤ expectedFrame := Nat.le_max_right _ _
    change (if expectedFrame = 0 then 0 else expectedFrame+1) ≤ _ at space
    split_ifs at space <;> omega
  obtain ⟨destinationTarget,saved,header,moved,calleeCode,calleeSize,calleeBs,calleeBsPost,
    calleeIndex,calleeIndexPost,savedHandler,destinationRun,savedRun,pushRun,moveRun,
    savedRelation,prePushRelation,headerRelation,calleeCompile,calleeBitmapLength,
    calleeBitmapBound,calleeBitmapPrefix,calleeLocalsSize,found,savedLookup,headerState,
    savedSpace,_,_⟩ := prepareHandlerCalleeDestination ac k f frame values names retCode l1 l2
      dest args handlerVar h1 h2 handlerCode source target lens xs args1 prog ss envs bs
      savedBitmaps n savedIndex destinationCode savedCode destination guards related conventions
      maximum destinationCompile savedCompile bitmapLength bitmapBound bitmapPrefix room
      location countBound
  obtain ⟨body,calleeFrame,codeEq,bodyCompile,shape,argumentBound,bodyMaximum,frameEq⟩ :=
    calleeBodyCompilation ac k args1.length prog calleeBs calleeBsPost calleeIndex
      calleeIndexPost calleeCode calleeSize calleeCompile
  have frameSpace : calleeSize ≤ (pushedHandlerState saved h1 h2 k savedHandler).stackSpace := by
    change calleeSize ≤ saved.stackSpace-3
    rw [savedSpace]
    change calleeFrame = expectedFrame at frameEq
    rw [frameEq] at shape
    change (if expectedFrame = 0 then 0 else expectedFrame+1) ≤ _ at space
    split_ifs at shape space <;> omega
  obtain ⟨movedAgain,entry,moveAgain,allocateRun,entryRelation⟩ := enterHandlerCallee ac k f frame
    calleeSize calleeFrame values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode
    savedHandler source saved lens xs args1 prog ss envs destinationCode destination guards
    savedRelation prePushRelation conventions maximum destinationCompile savedLookup
    (by rw [savedSpace]; exact room) shape calleeLocalsSize argumentBound frameSpace
  rw [← headerState] at moveAgain
  have movedEq : movedAgain = moved := congrArg Prod.snd (moveAgain.symm.trans moveRun)
  subst movedAgain
  have destinationMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    destinationCode target destinationTarget none destinationRun
  have savedMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    savedCode destinationTarget saved none savedRun
  have headerMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (pushHandlerNative false h1 h2 (k,f,frame)) saved header none pushRun
  have movedMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (stackHandlerArgsNative false destination (args.length+1) (k,f,frame)) header moved none moveRun
  have allocationMono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (.stackAlloc (calleeSize-(args1.length-k)))
    (StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)) entry none allocateRun
  have allocationBitmaps : moved.bitmaps.IsPrefix entry.bitmaps := allocationMono.1
  have allocationCode : sptSubspt moved.code entry.code := allocationMono.2
  have bitmapGrowth := destinationMono.1.trans (savedMono.1.trans
    (headerMono.1.trans (movedMono.1.trans allocationBitmaps)))
  have entryBitmapBound := calleeBitmapBound.trans bitmapGrowth.length_le
  have entryBitmapPrefix := calleeBitmapPrefix.trans
    (bitmapGrowth.drop (calleeIndex-(appListAppend calleeBs).length))
  have bodyLabels : ∀ label, StackSem.getLabelsExact body label →
      StackSem.locCheckExact entry.code label := by
    intro label member
    apply LocationLabels.locCheckSubset moved.code entry.code allocationCode label
    apply StackPropsCodeLabels.findCodeImpGetLabels destination (moved.regs.eraseEq 0)
      moved.code calleeCode found label
    rw [codeEq,StackSem.getLabelsExact]
    exact Or.inr member
  obtain ⟨_,_,_,_,_,_,_,_,_,_,bodyConventions,bodyFlat,_⟩ :=
    CallReturning.calleeCompilation ac k f frame values names retCode l1 l2 dest args
      source target lens xs args1 prog ss envs guards related
  have bodyNotError := handlerCalleeNotError values names retCode l1 l2 dest args
    (some (handlerVar,handlerCode,h1,h2)) source sourcePost bodyPost result bodyResult
    xs args1 prog ss envs guards nonzero wholeExecution notError bodyRun
  have simulation := hypotheses.2.2 xs args1 prog ss envs ⟨guards,nonzero⟩
  obtain ⟨extra,clockBound,targetPost,targetResult,execution,conclusion⟩ :=
    simulation k calleeSize calleeFrame bodyPost entry bodyResult calleeBs calleeBsPost
      calleeIndex calleeIndexPost body (frame :: lens)
      ⟨bodyRun,bodyNotError,entryRelation,bodyConventions,bodyFlat,bodyCompile,
        calleeBitmapLength,entryBitmapBound,entryBitmapPrefix,bodyLabels,bodyMaximum⟩
  have allocationClock (bump : Nat) : StackSemEvaluate.evaluate
      (.stackAlloc (calleeSize-(args1.length-k)),
        {StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
          with clock := (StackSemStateOps.decClock moved).clock + bump}) =
      (none,{entry with clock := entry.clock + bump}) := by
    have success := allocateRun
    rw [StackSemEvaluate.evaluate_stackAlloc] at success
    split_ifs at success with disabled insufficient
    · cases (Prod.mk.inj success).1
    · cases (Prod.mk.inj success).1
    obtain ⟨_,rfl⟩ := Prod.mk.inj success
    rw [StackSemEvaluate.evaluate_stackAlloc,if_neg disabled,if_neg insufficient]
    rfl
  have calleeExecution : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved)
        with clock := (StackSemStateOps.decClock moved).clock + extra}) =
      (targetResult,targetPost) := by
    rw [codeEq,StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,
      allocationClock extra]
    exact execution
  exact ⟨destinationTarget,saved,header,moved,entry,targetPost,calleeCode,body,calleeSize,
    calleeFrame,extra,targetResult,destinationRun,savedRun,pushRun,moveRun,found,codeEq,
    allocateRun,execution,calleeExecution,conclusion,clockBound⟩

theorem sourceHandlerReturningContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location : WordLocW width) (returned : List (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) source =
      (result, sourcePost)) (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2)) (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returned), bodyPost)) :
    ∃ (gc : List (Nat × WordLocW width)) (tail : List (WordSemStackFrame width))
      (popped : WordSemStateFiniteExact width (Nat × C) F),
      bodyPost.stack = .stackFrame source.localsSize (sptToAList envs.1) gc (some (source.handler,h1,h2)) :: tail ∧
      ((wordSemEnvToList envs.2 source.permute).1).map Prod.fst = gc.map Prod.fst ∧
      WordSemStackEq.sKeyEq source.stack tail ∧ bodyPost.handler = source.stack.length ∧
      popped = {bodyPost with
        locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
        stack := tail, localsSize := source.localsSize, handler := source.handler} ∧
      WordSemStateFiniteExact.popEnv bodyPost = some popped ∧
      sptDomainEqUnion popped.locals envs.1 envs.2 ∧
      ¬ (location ≠ .loc l1 l2 ∨ returned.length ≠ values.length) ∧
      WordSemStateFiniteExact.evaluate retCode (WordSemStateFiniteExact.setVars values returned popped) =
        (result, sourcePost) ∧
      SimulationB ac retCode (WordSemStateFiniteExact.setVars values returned popped) returnBudget := by
  obtain ⟨gc, tail, frame, gcKeys, tailKeys, handler, popRun, domain⟩ :=
    returnedHandlerCallerFrame prog source bodyPost envs args1 ss
      handlerVar h1 h2 handlerCode location returned bodyRun
  let popped : WordSemStateFiniteExact width (Nat × C) F := {bodyPost with
    locals := sptUnion (sptFromAList gc) (sptFromAList (sptToAList envs.1)),
    stack := tail, localsSize := source.localsSize, handler := source.handler}
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

theorem sourceHandlerExceptionContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (location value : WordLocW width)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (nonzero : source.clock ≠ 0)
    (execution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost)) :
    ¬ location ≠ .loc h1 h2 ∧ sptDomainEqUnion bodyPost.locals envs.1 envs.2 ∧
    WordSemStateFiniteExact.evaluate handlerCode
      (WordSemStateFiniteExact.setVar handlerVar value bodyPost) = (result,sourcePost) ∧
    SimulationB ac handlerCode (WordSemStateFiniteExact.setVar handlerVar value bodyPost) handlerBudget := by
  have originalGuards := guards
  obtain ⟨get,bad,find,valid,cut⟩ := originalGuards
  rw [WordSemStateFiniteExact.evaluate] at execution
  simp only [get,bad,Bool.false_eq_true,if_false,find,valid,cut] at execution
  rw [dif_neg nonzero,WordSemStateFiniteExact.fix_clock_evaluate,bodyRun] at execution
  simp only at execution
  by_cases invalid : location ≠ .loc h1 h2
  · rw [if_pos invalid] at execution
    exact False.elim (notError (Prod.mk.inj execution).1.symm)
  rw [if_neg invalid] at execution
  by_cases domain : sptDomainEqUnion bodyPost.locals envs.1 envs.2
  · rw [if_pos domain] at execution
    exact ⟨invalid,domain,execution,ih.2.1 xs args1 prog ss envs location value bodyPost
      ⟨guards,nonzero,bodyRun,invalid,domain⟩⟩
  · rw [if_neg domain] at execution
    exact False.elim (notError (Prod.mk.inj execution).1.symm)

theorem simulateHandlerNormalContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location : WordLocW width) (returnedValues : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returnedValues),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.result location returnedValues)) (some (.result location)) (payload::lens))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false retCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ extraClock targetPost targetResult,
      StackSemEvaluate.evaluate
        (copyRetNative false true (k,frame,payload) values
          (popHandlerNative false (k,frame,payload) compiled),
          {target with clock := target.clock+extraClock}) = (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      extraClock ≤ returnBudget := by
  obtain ⟨gc,rest,popped,sourceFrame,keys,tailKeys,handlerEq,poppedEq,popRun,domain,
    valid,sourceContinuation,continuationIH⟩ := sourceHandlerReturningContinuation
      ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
      result xs args1 prog ss envs location returnedValues guards ih nonzero wholeRun notError bodyRun
  have lengthEq : returnedValues.length = values.length := by omega
  obtain ⟨restoredSource,restored,restoredPop,restoreRun,restoredRelation⟩ :=
    restoreHandlerCallerFromBodyReturn ac k frame payload source bodyPost originalTarget target lens prior
      values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs guards
      conventions maximum location returnedValues lengthEq bodyRun calleeSize calleeFrame bodyConclusion
  have sourceSame : restoredSource = popped := Option.some.inj (restoredPop.symm.trans popRun)
  rw [sourceSame] at restoredRelation
  have mono := Compiler.Backend.StackProps.EvaluateMono.evaluateMono
    (copyRetNative false true (k,frame,payload) values
      (popHandlerNative false (k,frame,payload) .skip)) target restored none restoreRun
  have restoredBitmapBound : n-(appListAppend bs).length ≤ restored.bitmaps.length :=
    bitmapBound.trans mono.1.length_le
  have restoredBitmapPrefix : (appListAppend bsPost).IsPrefix
      (restored.bitmaps.drop (n-(appListAppend bs).length)) := bitmapPrefix.trans (mono.1.drop _)
  have restoredLabels : ∀ loc, StackSem.getLabelsExact compiled loc →
      StackSem.locCheckExact restored.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset target.code restored.code mono.2 loc (labels loc member)
  have retConventions := (CallReturning.returningConventions k values names retCode l1 l2 dest args
    (conventionsWithoutHandler k values names retCode l1 l2 dest args
      (some (handlerVar,handlerCode,h1,h2)) conventions)).1
  have retFlat : flatExpConventions retCode = true := by
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    exact flat.1
  have retMax : maxVarHOL retCode < 2*payload+2*k := by
    simp only [maxVarHOL,Flapjack.WordAlloc.max3Eq] at maximum
    omega
  obtain ⟨extraClock,clockBound,targetPost,targetResult,continuationRun,conclusion⟩ :=
    continuationIH k frame payload sourcePost restored result bs bsPost n nPost compiled lens
      ⟨sourceContinuation,notError,restoredRelation,retConventions,retFlat,compilation,
        lengthBound,restoredBitmapBound,restoredBitmapPrefix,restoredLabels,retMax⟩
  have extendedRestore := Compiler.Backend.StackProps.evaluateAddClock extraClock
    (copyRetNative false true (k,frame,payload) values
      (popHandlerNative false (k,frame,payload) .skip)) target none restored ⟨restoreRun,by simp⟩
  have sourceHandler : (WordSemStateFiniteExact.setVars values returnedValues popped).handler =
      source.handler := by rw [poppedEq]; rfl
  refine ⟨extraClock,targetPost,targetResult,?_,?_,clockBound⟩
  · rw [handlerRestoreContinuationSequence,StackSemEvaluate.evaluate_seq,
      StackSemEvaluateClock.fixClockEvaluate,extendedRestore]
    exact continuationRun
  · unfold compCorrectResult at conclusion ⊢
    rw [sourceHandler] at conclusion
    exact conclusion

theorem restoreHandlerCallerFromBodyException {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.exception location value)) (some (.exception location)) (payload::lens)) :
    stateRel ac k frame payload (WordSemStateFiniteExact.setVar handlerVar value bodyPost)
      target lens 0 ∧ bodyPost.handler = source.handler := by
  have nonempty : ¬ sptDomainEmpty names.1 := by
    intro empty
    exact guards.2.2.2.1 (Or.inl empty)
  obtain ⟨valid,domain,sourceContinuation,continuationIH⟩ := sourceHandlerExceptionContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location value guards ih nonzero wholeRun notError bodyRun
  have length := CallReturnSupport.stateRelImpLength ac k frame payload source originalTarget lens 0 prior
  simp only [compCorrectResult,compileResult,Option.map_some,ne_eq,not_true_eq_false,
    ↓reduceIte] at bodyConclusion
  obtain ⟨nonGc,gc,related,locals,returned⟩ := bodyConclusion
  have relatedFull : stateRel ac k 0 0 (pushLocals nonGc gc bodyPost) target (payload::lens) 0 := by
    have lensEq : (payload::lens).drop ((payload::lens).length -
        ((WordSemStateFiniteExact.callEnv args1 ss
          (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
            (WordSemStateFiniteExact.decClock source))).handler+1)) = payload::lens := by
      simp only [WordSemStateFiniteExact.callEnv,WordSemStateFiniteExact.pushEnv,
        WordSemStateFiniteExact.decClock,List.length_cons,length,Nat.sub_self,List.drop_zero]
    rwa [lensEq] at related
  have restored := restoreExceptionalHandlerCallerStateRel ac k frame payload source bodyPost
    originalTarget target lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args
    envs guards.2.2.2.2 nonempty conventions maximum nonGc gc value relatedFull locals domain returned
  obtain ⟨originalGc,sizeEq,gcKeys,sourceLocals,tailKeys,handlerEq⟩ := exceptionalHandlerCallerFrame
    prog source bodyPost envs args1 ss handlerVar h1 h2 handlerCode location value bodyRun
  exact ⟨restored,handlerEq⟩

theorem simulateHandlerExceptionContinuation {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.exception location value)) (some (.exception location)) (payload::lens))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false handlerCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ extraClock targetPost targetResult,
      StackSemEvaluate.evaluate
        (compiled,
          {target with clock := target.clock+extraClock}) = (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      extraClock ≤ handlerBudget := by
  obtain ⟨valid,domain,sourceContinuation,continuationIH⟩ := sourceHandlerExceptionContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location value guards ih nonzero wholeRun notError bodyRun
  obtain ⟨restoredRelation,handlerEq⟩ := restoreHandlerCallerFromBodyException ac k frame payload
    source sourcePost bodyPost originalTarget target lens prior values names retCode handlerCode
    l1 l2 h1 h2 handlerVar dest args conventions maximum xs args1 prog ss envs guards ih nonzero
    result wholeRun notError location value bodyRun calleeSize calleeFrame bodyConclusion
  have handlerConventions : postAllocConventionsHOL k handlerCode = true := by
    simp only [postAllocConventionsHOL,everyVarHOL,everyStackVarHOL,
      callArgConventionHOL,Bool.and_eq_true] at conventions ⊢
    aesop (config := { enableSimp := false })
  have handlerFlat : flatExpConventions handlerCode = true := by
    simp only [flatExpConventions,Bool.and_eq_true] at flat
    exact flat.2
  have handlerMax : maxVarHOL handlerCode < 2*payload+2*k := by
    simp only [maxVarHOL,Flapjack.WordAlloc.max3Eq] at maximum
    omega
  obtain ⟨extraClock,clockBound,targetPost,targetResult,continuationRun,conclusion⟩ :=
    continuationIH k frame payload sourcePost target result bs bsPost n nPost compiled lens
      ⟨sourceContinuation,notError,restoredRelation,handlerConventions,handlerFlat,compilation,
        lengthBound,bitmapBound,bitmapPrefix,labels,handlerMax⟩
  refine ⟨extraClock,targetPost,targetResult,continuationRun,?_,clockBound⟩
  unfold compCorrectResult at conclusion ⊢
  change bodyPost.handler = source.handler at handlerEq
  simp only [WordSemStateFiniteExact.setVar,handlerEq] at conclusion
  exact conclusion

theorem normalHandlerCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location : WordLocW width) (returnedValues : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returnedValues),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.result location returnedValues)) (some (.result location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode handlerTarget : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result location),target))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false retCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ continuationExtra targetPost targetResult,
      StackSemEvaluate.evaluate
        (.call (some (.seq .skip (copyRetNative false true (k,frame,payload) values
          (popHandlerNative false (k,frame,payload) compiled)),0,l1,l2))
          destination (some (handlerTarget,h1,h2)),
          {moved with clock := moved.clock+(bodyExtra+continuationExtra)}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      continuationExtra ≤ returnBudget := by
  obtain ⟨gc,rest,popped,sourceFrame,keys,tailKeys,handlerEq,poppedEq,popRun,domain,
    valid,sourceContinuation,continuationIH⟩ := sourceHandlerReturningContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location returnedValues guards ih nonzero wholeRun notError bodyRun
  have locationEq : location = .loc l1 l2 := by
    by_contra different
    exact valid (Or.inl different)
  obtain ⟨continuationExtra,targetPost,targetResult,continuationRun,conclusion,clockBound⟩ :=
    simulateHandlerNormalContinuation ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location returnedValues
      bodyRun calleeSize calleeFrame bodyConclusion bs bsPost n nPost compiled compilation lengthBound
      bitmapBound bitmapPrefix labels
  have normalRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result (.loc l1 l2)),target) := by
    simpa only [locationEq] using calleeRun
  have skipped : StackSemEvaluate.evaluate
      (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) compiled)),
        {target with clock := target.clock+continuationExtra}) = (targetResult,targetPost) := by
    rw [CallReturnEval.seq_skip_left]
    exact continuationRun
  exact ⟨continuationExtra,targetPost,targetResult,
    returningHandlerCallNormalRun moved target targetPost l1 l2 h1 h2 bodyExtra continuationExtra
      destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) compiled))) handlerTarget targetResult
      found movedNonzero normalRun skipped,conclusion,clockBound⟩

theorem exceptionHandlerCallFromCallee {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.exception location value)) (some (.exception location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode continuationTarget : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (movedNonzero : moved.clock ≠ 0)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.exception location),target))
    (bs bsPost : AppList (BitVec width)) (n nPost : Nat) (compiled : HolProg width)
    (compilation : compNative ac false handlerCode (bs,n) (k,frame,payload) = (compiled,(bsPost,nPost)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend bsPost).IsPrefix (target.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc) :
    ∃ handlerExtra targetPost targetResult,
      StackSemEvaluate.evaluate
        (.call (some (continuationTarget,0,l1,l2)) destination (some (compiled,h1,h2)),
          {moved with clock := moved.clock+(bodyExtra+handlerExtra)}) = (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      handlerExtra ≤ handlerBudget := by
  obtain ⟨valid,domain,sourceContinuation,continuationIH⟩ := sourceHandlerExceptionContinuation
    ac values names retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost bodyPost
    result xs args1 prog ss envs location value guards ih nonzero wholeRun notError bodyRun
  have locationEq : location = .loc h1 h2 := by
    by_contra different
    exact valid different
  obtain ⟨handlerExtra,targetPost,targetResult,handlerRun,conclusion,clockBound⟩ :=
    simulateHandlerExceptionContinuation ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location value
      bodyRun calleeSize calleeFrame bodyConclusion bs bsPost n nPost compiled compilation lengthBound
      bitmapBound bitmapPrefix labels
  have exceptionRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.exception (.loc h1 h2)),target) := by
    simpa only [locationEq] using calleeRun
  exact ⟨handlerExtra,targetPost,targetResult,
    returningHandlerCallExceptionRun moved target targetPost l1 l2 h1 h2 bodyExtra handlerExtra
      destination calleeCode continuationTarget compiled targetResult found movedNonzero exceptionRun
      handlerRun,conclusion,clockBound⟩

theorem normalCompiledHandlerCallFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location : WordLocW width) (returnedValues : List (WordLocW width))
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.result location returnedValues),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.result location returnedValues)) (some (.result location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.result location),target))
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBs,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ originalTarget.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (originalTarget.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact originalTarget.code loc)
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
      (none,moved)) :
    ∃ extra targetPost targetResult,
      StackSemEvaluate.evaluate (compiled,{originalTarget with clock := originalTarget.clock+extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      extra ≤ bodyExtra + returnBudget := by
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBs,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free originalTarget originalTarget.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
    (Prod.map id (fun state => {state with clock := originalTarget.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = originalTarget.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [clockEq,← prior.1]
    exact nonzero
  have growth := handlerCalleeHistoryGrowth originalTarget moved target
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))))
    calleeCode l1 l2 bodyExtra (some (.result location)) preludeRun calleeRun
  obtain ⟨continuationLength,continuationBound,continuationPrefix,continuationLabels⟩ :=
    handlerReturningCompilationContext ac k frame payload values names retCode handlerCode l1 l2 h1 h2 handlerVar
      dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget destinationCompile savedCompile
      returnCompile handlerCompile compilation lengthBound bitmapBound bitmapPrefix labels
  have bodyLabels : ∀ loc, StackSem.getLabelsExact returnCode loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset originalTarget.code target.code growth.2 loc
      (continuationLabels loc member)
  obtain ⟨continuationExtra,targetPost,targetResult,callRun,conclusion,clockBound⟩ :=
    normalHandlerCallFromCallee ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location returnedValues
      bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode handlerTarget bodyExtra found movedNonzero calleeRun
      savedBs retBs savedIndex retIndex returnCode returnCompile
      continuationLength (continuationBound.trans growth.1.length_le)
      (continuationPrefix.trans (growth.1.drop _)) bodyLabels
  exact ⟨bodyExtra+continuationExtra,targetPost,targetResult,
    completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
      h1 h2 dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget moved targetPost
      (bodyExtra+continuationExtra) targetResult destinationCompile savedCompile returnCompile handlerCompile
      compilation preludeRun callRun,conclusion,by omega⟩

theorem exceptionCompiledHandlerCallFromHistory {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (originalTarget target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (prior : stateRel ac k frame payload source originalTarget lens 0)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode handlerCode : WordLangProgHOL (BitVec width))
    (l1 l2 h1 h2 handlerVar : Nat) (dest : Option Nat) (args : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    {bodyBudget returnBudget handlerBudget : Nat}
    (ih : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget)
    (conventions : postAllocConventionsHOL k
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) < 2*payload+2*k)
    (nonzero : source.clock ≠ 0) (result : Option (WordSemResult width))
    (wholeRun : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (location value : WordLocW width)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) =
      (some (.exception location value),bodyPost))
    (calleeSize calleeFrame : Nat)
    (bodyConclusion : compCorrectResult ac k calleeSize calleeFrame
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) bodyPost target
      (some (.exception location value)) (some (.exception location)) (payload::lens))
    (moved : StackSemStateFiniteExact width C F) (destination : Sum Nat Nat)
    (calleeCode : HolProg width) (bodyExtra : Nat)
    (found : StackSemControl.findCode destination (moved.regs.eraseEq 0) moved.code = some calleeCode)
    (calleeRun : StackSemEvaluate.evaluate
      (calleeCode,{StackSemStateOps.setVar 0 (.loc l1 l2) (StackSemStateOps.decClock moved) with
        clock := (StackSemStateOps.decClock moved).clock+bodyExtra}) =
      (some (.exception location),target))
    (bs savedBs retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width)
    (destinationCompile : callDestNative dest args (k,frame,payload) = (destinationCode,destination))
    (savedCompile : wLiveNative names (bs,n) (k,frame,payload) = (savedCode,(savedBs,savedIndex)))
    (returnCompile : compNative ac false retCode (savedBs,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (lengthBound : (appListAppend bs).length ≤ n)
    (bitmapBound : n-(appListAppend bs).length ≤ originalTarget.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (originalTarget.bitmaps.drop (n-(appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact originalTarget.code loc)
    (preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
      (none,moved)) :
    ∃ extra targetPost targetResult,
      StackSemEvaluate.evaluate (compiled,{originalTarget with clock := originalTarget.clock+extra}) =
        (targetResult,targetPost) ∧
      compCorrectResult ac k frame payload source sourcePost targetPost result targetResult lens ∧
      extra ≤ bodyExtra + handlerBudget := by
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBs,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free originalTarget originalTarget.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget) =
    (Prod.map id (fun state => {state with clock := originalTarget.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),originalTarget)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = originalTarget.clock :=
    congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by
    rw [clockEq,← prior.1]
    exact nonzero
  have growth := handlerCalleeHistoryGrowth originalTarget moved target
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))))
    calleeCode l1 l2 bodyExtra (some (.exception location)) preludeRun calleeRun
  obtain ⟨continuationLength,continuationBound,continuationPrefix,continuationLabels⟩ :=
    handlerExceptionCompilationContext ac k frame payload values names retCode handlerCode l1 l2 h1 h2 handlerVar
      dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget destinationCompile savedCompile
      returnCompile handlerCompile compilation lengthBound bitmapBound bitmapPrefix labels
  have bodyLabels : ∀ loc, StackSem.getLabelsExact handlerTarget loc →
      StackSem.locCheckExact target.code loc := by
    intro loc member
    exact LocationLabels.locCheckSubset originalTarget.code target.code growth.2 loc
      (continuationLabels loc member)
  obtain ⟨continuationExtra,targetPost,targetResult,callRun,conclusion,clockBound⟩ :=
    exceptionHandlerCallFromCallee ac k frame payload source sourcePost bodyPost originalTarget target
      lens prior values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1 prog ss envs
      guards ih conventions flat maximum nonzero result wholeRun notError location value
      bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) bodyExtra found movedNonzero calleeRun
      retBs handlerBs retIndex handlerIndex handlerTarget handlerCompile
      continuationLength (continuationBound.trans growth.1.length_le)
      (continuationPrefix.trans (growth.1.drop _)) bodyLabels
  exact ⟨bodyExtra+continuationExtra,targetPost,targetResult,
    completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
      h1 h2 dest args bs savedBs retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
      returnCode handlerTarget compiled destination originalTarget moved targetPost
      (bodyExtra+continuationExtra) targetResult destinationCompile savedCompile returnCompile handlerCompile
      compilation preludeRun callRun,conclusion,by omega⟩

theorem simulateSuccessfulHandlerCall {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost bodyPost : WordSemStateFiniteExact width (Nat × C) F)
    (result bodyResult : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k frame payload source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * payload + 2 * k)
    (destinationCompile : callDestNative dest args (k, frame, payload) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, frame, payload) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (room : 3 ≤ target.stackSpace)
    (space : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
      else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3)
    (nonzero : source.clock ≠ 0)
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    (bodyRun : WordSemStateFiniteExact.evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss
        (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
          (WordSemStateFiniteExact.decClock source))) = (bodyResult,bodyPost))
    {bodyBudget returnBudget handlerBudget : Nat}
    (hypotheses : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget) :
    ∃ extra targetFinal targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
        (targetResult,targetFinal) ∧
      compCorrectResult ac k frame payload source sourcePost targetFinal result targetResult lens ∧
      extra ≤ bodyBudget + max returnBudget handlerBudget := by
  have returnPrefix := compImpIsPrefix ac false retCode (savedBitmaps,savedIndex) (k,frame,payload)
    returnCode (retBs,retIndex) returnCompile
  have handlerPrefix := compImpIsPrefix ac false handlerCode (retBs,retIndex) (k,frame,payload)
    handlerTarget (handlerBs,handlerIndex) handlerCompile
  have savedPrefix := returnPrefix.trans (handlerPrefix.trans bitmapPrefix)
  have handlerLocation : StackSem.locCheckExact target.code (h1,h2) := by
    apply labels (h1,h2)
    have shape := compilation
    simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
      Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
    obtain ⟨rfl,_⟩ := shape
    simp only [StackSem.getLabelsExact,or_true,true_or]
  obtain ⟨destinationTarget,saved,header,moved,entry,calleeTarget,calleeCode,body,
    calleeSize,calleeFrame,bodyExtra,targetResult,destinationRun,savedRun,pushRun,argumentsRun,
    found,calleeShape,allocationRun,bodyTargetRun,calleeRun,bodyConclusion,bodyClockBound⟩ :=
    simulateHandlerCalleeBody ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source sourcePost bodyPost result bodyResult target lens xs args1 prog ss envs bs
      savedBitmaps n savedIndex destinationCode savedCode destination guards related conventions maximum
      destinationCompile savedCompile bitmapLength bitmapBound savedPrefix room handlerLocation space
      nonzero wholeExecution notError bodyRun hypotheses
  have preludeRun : StackSemEvaluate.evaluate
      (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
        (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
      (none,moved) := by
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,destinationRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,savedRun]
    simp only
    rw [StackSemEvaluate.evaluate_seq,StackSemEvaluateClock.fixClockEvaluate,pushRun]
    exact argumentsRun
  have free := completeHandlerPreludeClockFree (C := C) (F := F) k frame payload h1 h2 dest args names
    (bs,n) (savedBitmaps,savedIndex) destinationCode savedCode destination destinationCompile savedCompile
  have fixed := free target target.clock
  change StackSemEvaluate.evaluate
    (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
      (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target) =
    (Prod.map id (fun state => {state with clock := target.clock}))
      (StackSemEvaluate.evaluate
        (.seq destinationCode (.seq savedCode (.seq (pushHandlerNative false h1 h2 (k,frame,payload))
          (stackHandlerArgsNative false destination (args.length+1) (k,frame,payload)))),target)) at fixed
  rw [preludeRun] at fixed
  have clockEq : moved.clock = target.clock := congrArg (fun state => state.clock) (Prod.mk.inj fixed).2
  have movedNonzero : moved.clock ≠ 0 := by rw [clockEq,← related.1]; exact nonzero
  have finishTerminal
      (terminal : targetResult = some .timeOut ∨ (∃ value, targetResult = some (.halt value)) ∨
        ∃ event, targetResult = some (.finalFFI event)) :
      ∃ extra targetFinal finalResult,
        StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
          (finalResult,targetFinal) ∧
        compCorrectResult ac k frame payload source sourcePost targetFinal result finalResult lens ∧
        extra ≤ bodyBudget + max returnBudget handlerBudget := by
    obtain ⟨callRun,conclusion⟩ := terminalHandlerCallFromCallee ac k frame payload calleeSize calleeFrame
      values names retCode handlerCode l1 l2 handlerVar h1 h2 dest args source sourcePost bodyPost
      result bodyResult target moved calleeTarget targetResult lens xs args1 prog ss envs bodyExtra
      destination calleeCode (.seq .skip (copyRetNative false true (k,frame,payload) values
        (popHandlerNative false (k,frame,payload) returnCode))) handlerTarget guards related nonzero
      wholeExecution bodyRun found movedNonzero calleeRun bodyConclusion terminal
    exact ⟨bodyExtra,calleeTarget,targetResult,
      completeHandlerCallFromPrelude ac k frame payload values names retCode handlerCode l1 l2 handlerVar
        h1 h2 dest args bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode
        savedCode returnCode handlerTarget compiled destination target moved calleeTarget bodyExtra targetResult
        destinationCompile savedCompile returnCompile handlerCompile compilation preludeRun callRun,conclusion,by omega⟩
  by_cases matching : bodyResult.map compileResult = targetResult
  · have outcomes := handlerCalleeOutcomeCases values names retCode handlerCode l1 l2 handlerVar h1 h2
      dest args source sourcePost bodyPost result bodyResult xs args1 prog ss envs guards nonzero
      wholeExecution bodyRun notError
    rcases outcomes with ⟨location,returned,rfl⟩ | ⟨location,value,rfl⟩ | timeout | resource | ⟨event,ffi⟩
    · have targetEq : targetResult = some (.result location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      obtain ⟨extra, targetPost, targetResult, run, conclusion, clockBound⟩ :=
        normalCompiledHandlerCallFromHistory ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location returned bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun
      exact ⟨extra, targetPost, targetResult, run, conclusion, by omega⟩
    · have targetEq : targetResult = some (.exception location) := by
        simpa only [Option.map_some,compileResult] using matching.symm
      subst targetResult
      obtain ⟨extra, targetPost, targetResult, run, conclusion, clockBound⟩ :=
        exceptionCompiledHandlerCallFromHistory ac k frame payload source sourcePost bodyPost target
        calleeTarget lens related values names retCode handlerCode l1 l2 h1 h2 handlerVar dest args xs args1
        prog ss envs guards hypotheses conventions flat maximum nonzero result wholeExecution notError
        location value bodyRun calleeSize calleeFrame bodyConclusion moved destination calleeCode
        bodyExtra found calleeRun bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex
        destinationCode savedCode returnCode handlerTarget compiled destinationCompile savedCompile
        returnCompile handlerCompile compilation bitmapLength bitmapBound bitmapPrefix labels preludeRun
      exact ⟨extra, targetPost, targetResult, run, conclusion, by omega⟩
    · apply finishTerminal
      left
      simpa only [timeout,Option.map_some,compileResult] using matching.symm
    · apply finishTerminal
      right; left
      exact ⟨.word 1,by simpa only [resource,Option.map_some,compileResult] using matching.symm⟩
    · apply finishTerminal
      right; right
      exact ⟨event,by simpa only [ffi,Option.map_some,compileResult] using matching.symm⟩
  · have mismatch := bodyConclusion
    unfold compCorrectResult at mismatch
    rw [if_pos matching] at mismatch
    exact finishTerminal (Or.inr (Or.inl ⟨.word 2,mismatch.1⟩))

theorem simulateHandlerCallWithGuards {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k frame payload : Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source sourcePost : WordSemStateFiniteExact width (Nat × C) F)
    (result : Option (WordSemResult width))
    (target : StackSemStateFiniteExact width C F) (lens : List Nat)
    (xs args1 : List (WordLocW width)) (prog : WordLangProgHOL (BitVec width))
    (ss : Option Nat) (envs : Spt (WordLocW width) × Spt (WordLocW width))
    (bs savedBitmaps retBs handlerBs : AppList (BitVec width))
    (n savedIndex retIndex handlerIndex : Nat)
    (destinationCode savedCode returnCode handlerTarget compiled : HolProg width) (destination : Sum Nat Nat)
    (guards : CallReturning.SourceGuards values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (related : stateRel ac k frame payload source target lens 0)
    (conventions : postAllocConventionsHOL k
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) = true)
    (flat : flatExpConventions
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) = true)
    (maximum : maxVarHOL
      (.call (some (values, names, retCode, l1, l2)) dest args (some (handlerVar,handlerCode,h1,h2))) < 2 * payload + 2 * k)
    (destinationCompile : callDestNative dest args (k, frame, payload) = (destinationCode, destination))
    (savedCompile : wLiveNative names (bs, n) (k, frame, payload) = (savedCode, (savedBitmaps, savedIndex)))
    (returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,frame,payload) =
      (returnCode,(retBs,retIndex)))
    (handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,frame,payload) =
      (handlerTarget,(handlerBs,handlerIndex)))
    (compilation : compNative ac false
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) (bs,n) (k,frame,payload) =
      (compiled,(handlerBs,handlerIndex)))
    (bitmapLength : (appListAppend bs).length ≤ n)
    (bitmapBound : n - (appListAppend bs).length ≤ target.bitmaps.length)
    (bitmapPrefix : (appListAppend handlerBs).IsPrefix
      (target.bitmaps.drop (n - (appListAppend bs).length)))
    (labels : ∀ loc, StackSem.getLabelsExact compiled loc → StackSem.locCheckExact target.code loc)
    (wholeExecution : WordSemStateFiniteExact.evaluate
      (.call (some (values,names,retCode,l1,l2)) dest args
        (some (handlerVar,handlerCode,h1,h2))) source = (result,sourcePost))
    (notError : result ≠ some .error)
    {bodyBudget returnBudget handlerBudget : Nat}
    (hypotheses : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget) :
    ∃ extra targetFinal targetResult,
      StackSemEvaluate.evaluate (compiled,{target with clock := target.clock+extra}) =
        (targetResult,targetFinal) ∧
      compCorrectResult ac k frame payload source sourcePost targetFinal result targetResult lens ∧
      extra ≤ bodyBudget + max returnBudget handlerBudget := by
  by_cases room : 3 ≤ target.stackSpace
  · by_cases arguments : Compiler.Backend.WordToStack.stackArgCount destination (args.length+1) k ≤
        target.stackSpace-3
    · by_cases zero : source.clock = 0
      · have location : StackSem.locCheckExact target.code (h1,h2) := by
          apply labels (h1,h2)
          have shape := compilation
          simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
            Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
          obtain ⟨rfl,_⟩ := shape
          simp only [StackSem.getLabelsExact,or_true,true_or]
        obtain ⟨targetPost,run,contract⟩ := compiledHandlerCallTimeout ac k frame payload values names
          retCode l1 l2 dest args handlerVar h1 h2 handlerCode source sourcePost result target lens xs
          args1 prog ss envs bs savedBitmaps retBs n savedIndex retIndex destinationCode savedCode
          returnCode destination guards related conventions maximum destinationCompile savedCompile
          returnCompile handlerBs handlerIndex handlerTarget handlerCompile room location bitmapLength
          bitmapBound compiled compilation wholeExecution arguments zero bitmapPrefix
        refine ⟨0,targetPost,some .timeOut,?_,contract,Nat.zero_le _⟩
        have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
        rwa [unchanged]
      · by_cases calleeSpace : (if max (maxVarHOL prog / 2 + 1-k) (args1.length-k) = 0 then 0
            else max (maxVarHOL prog / 2 + 1-k) (args1.length-k)+1) ≤ target.stackSpace-3
        · rcases bodyRun : WordSemStateFiniteExact.evaluate prog
            (WordSemStateFiniteExact.callEnv args1 ss
              (WordSemStateFiniteExact.pushEnv envs (some (handlerVar,handlerCode,h1,h2))
                (WordSemStateFiniteExact.decClock source))) with ⟨bodyResult,bodyPost⟩
          exact simulateSuccessfulHandlerCall ac k frame payload values names retCode l1 l2 dest args
            handlerVar h1 h2 handlerCode source sourcePost bodyPost result bodyResult target lens xs args1
            prog ss envs bs savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode
            savedCode returnCode handlerTarget compiled destination guards related conventions flat maximum
            destinationCompile savedCompile returnCompile handlerCompile compilation bitmapLength bitmapBound
            bitmapPrefix labels room calleeSpace zero wholeExecution notError bodyRun hypotheses
        · obtain ⟨targetPost,run,contract⟩ := compiledHandlerCalleeAllocationFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
            handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
            n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
            maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
            handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix labels
            room arguments zero (by omega)
          refine ⟨0,targetPost,some (.halt (.word 2)),?_,contract,Nat.zero_le _⟩
          have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
          rwa [unchanged]
    · obtain ⟨targetPost,run,contract⟩ := compiledHandlerArgumentsFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
        handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
        n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
        maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
        handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix labels
        room (by omega)
      refine ⟨0,targetPost,some (.halt (.word 2)),?_,contract,Nat.zero_le _⟩
      have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
      rwa [unchanged]
  · obtain ⟨targetPost,run,contract⟩ := compiledHandlerHeaderFailure ac k frame payload values names retCode l1 l2 dest args handlerVar h1 h2
      handlerCode source sourcePost result target lens xs args1 prog ss envs bs savedBitmaps retBs
      n savedIndex retIndex destinationCode savedCode returnCode destination guards related conventions
      maximum destinationCompile savedCompile returnCompile handlerBs handlerIndex handlerTarget compiled
      handlerCompile compilation wholeExecution bitmapLength bitmapBound bitmapPrefix (by omega)
    refine ⟨0,targetPost,some (.halt (.word 2)),?_,contract,Nat.zero_le _⟩
    have unchanged : {target with clock := target.clock+0} = target := by cases target; rfl
    rwa [unchanged]

theorem compCorrectCallReturningHandler {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handlerVar h1 h2 : Nat) (handlerCode : WordLangProgHOL (BitVec width))
    (source : WordSemStateFiniteExact width (Nat × C) F)
    {bodyBudget returnBudget handlerBudget : Nat}
    (hypotheses : InductionHypotheses ac values names retCode l1 l2 dest args
      handlerVar h1 h2 handlerCode source bodyBudget returnBudget handlerBudget) :
    SimulationB ac (.call (some (values,names,retCode,l1,l2)) dest args
      (some (handlerVar,handlerCode,h1,h2))) source
      (bodyBudget + max returnBudget handlerBudget) := by
  intro k f frame sourcePost target result bs bsPost n nPost compiled lens facts
  obtain ⟨execution,notError,related,conventions,flat,compilation,lengthBound,bitmapBound,
    bitmapPrefix,labels,maximum⟩ := facts
  obtain ⟨xs,args1,prog,ss,envs,guards⟩ := sourceGuardsOfNotErrorWithHandler values names retCode
    l1 l2 dest args (some (handlerVar,handlerCode,h1,h2)) source sourcePost result execution notError
  rcases destinationCompile : callDestNative (width := width) dest args (k,f,frame) with ⟨destinationCode,destination⟩
  rcases savedCompile : wLiveNative (width := width) names (bs,n) (k,f,frame) with ⟨savedCode,savedBitmaps,savedIndex⟩
  rcases returnCompile : compNative ac false retCode (savedBitmaps,savedIndex) (k,f,frame) with
    ⟨returnCode,retBs,retIndex⟩
  rcases handlerCompile : compNative ac false handlerCode (retBs,retIndex) (k,f,frame) with
    ⟨handlerTarget,handlerBs,handlerIndex⟩
  have shape := compilation
  simp only [compNative,destinationCompile,savedCompile,returnCompile,handlerCompile,
    Bool.false_eq_true,if_false,Prod.mk.injEq] at shape
  obtain ⟨_,rfl,rfl⟩ := shape
  obtain ⟨extra, targetFinal, targetResult, run, conclusion, clockBound⟩ :=
    simulateHandlerCallWithGuards ac k f frame values names retCode l1 l2 dest args
    handlerVar h1 h2 handlerCode source sourcePost result target lens xs args1 prog ss envs bs
    savedBitmaps retBs handlerBs n savedIndex retIndex handlerIndex destinationCode savedCode
    returnCode handlerTarget compiled destination guards related conventions flat maximum
    destinationCompile savedCompile returnCompile handlerCompile compilation lengthBound bitmapBound
    bitmapPrefix labels execution notError hypotheses
  exact ⟨extra, clockBound, targetFinal, targetResult, run, conclusion⟩

#print axioms compCorrectCallReturningHandler

end InitECandidate.Solver.Wave8Stage.WordToStackHandlerClock
