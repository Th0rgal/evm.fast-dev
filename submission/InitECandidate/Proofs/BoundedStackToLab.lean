import InitECandidate.Proofs.BoundedTarget
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileSemantics
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSemantics

namespace InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend.LabProps
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Clock-preserving `WordToWord` simulation: at any clock `k`, a non-error entry call
on `s` (with `s.code = sptFromAList wprog0`) produces the exact same result and FFI state
on `{ s with code := sptFromAList wprog }` at the same clock `k`. -/
theorem word_to_word_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (wconf : WordToWord.Config) (ac : AsmConfigExact width)
    (wprog0 : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (col : List (Option (Spt Nat)))
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (s : WordSemStateFiniteExact width C F) (start k : Nat)
    (hwtw : WordToWord.compile wconf ac wprog0 = (col, wprog))
    (hgc : WordSimp.gcFunConstOk s.gcFun)
    (hnic : WordProps.noInstallCode s.code)
    (hnac : WordProps.noAllocCode s.code)
    (hnmc : WordProps.noMtCode (sptFromAList wprog0))
    (hstack : s.stack = [])
    (hsc : s.code = sptFromAList wprog0)
    (hne : (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k }).1 ≠ some .error) :
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k, code := sptFromAList wprog }).1 =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        { s with clock := k }).1 ∧
    (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k, code := sptFromAList wprog }).2.ffi =
      (WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        { s with clock := k }).2.ffi := by
  have hext := WordToWord.code_rel_ext_word_to_word ac wprog0 wconf col wprog hwtw
  have hrel0 := WordToWord.no_mt_code_rel_ext _ _ ⟨hnmc, hext⟩
  have hdom0 : sptDomain (sptFromAList wprog0) = sptDomain (sptFromAList wprog) := by
    simp only [WordToWord.compile, Prod.mk.injEq] at hwtw
    obtain ⟨-, rfl⟩ := hwtw
    funext n
    simp only [sptDomain, sptLookup_sptFromAList]
    rw [WordToWord.sptAListLookup_isSome_map_fullCompileSingle _ _ _ _ wprog0 _
      (WordToWord.compile_zip_length wconf wprog0)]
  rw [← hsc] at hrel0 hdom0 hnmc
  exact WordToWord.compile_runs_agree s (sptFromAList wprog) start k
    hrel0 hnic hnac hnmc hdom0 hgc hstack hne

/-- Clocked `WordToStack` simulation under `wordLangSafeForSpace`: a non-error `WordSem`
entry call at clock `k` yields a `StackSem` entry call at clock `k + ck` with the exact
compiled result (`res.map compileResult`) and identical FFI state. -/
theorem word_to_stack_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k_reg : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F)
    (start k : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (related : WordToStackProofs.stateRel ac k_reg 0 0 s t [] 0)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace s start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ ck t1,
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k + ck }) =
        (res.map WordToStackProofs.CompCorrect.compileResult, t1) ∧
      s1.ffi = t1.ffi := by
  have sim := WordToStackProofs.StateRelSemantics.entrySimulationOfStateRel
    ac k_reg s t [] start related
  obtain ⟨ck, res1, t1, targetRun, outcome⟩ := sim k res s1 hrun hne
  rcases outcome with ⟨same, ffi⟩ | ⟨_, _, _, hover⟩
  · subst same
    exact ⟨ck, t1, targetRun, ffi⟩
  · obtain ⟨max, maxEq, maxLe⟩ := safe k res s1 hrun
    rw [maxEq] at hover
    simp only [Option.getD_some] at hover
    omega

/-- Clocked `StackRawCall` simulation: at any clock `k`, a non-error entry call on `source`
produces a target run on `{ source with code := sptFromAList (compile code), clock := k + extra }`
with the exact same result and FFI state. -/
theorem stack_rawcall_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { source with clock := clock }) =
      (result, post))
    (nonError : result ≠ some .error) :
    ∃ extra targetPost, StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        { source with code := sptFromAList (StackRawCall.compile code), clock := clock + extra }) =
      (result, targetPost) ∧ targetPost.ffi = post.ffi :=
  StackRawCall.CompileSemantics.entrySimulation code source start clock result post
    distinct sourceCode run nonError

/-- Clocked `StackAlloc` simulation: at any clock `k`, a non-error entry call on `s` produces
a target run at clock `k + ck` with the exact same result and FFI state. -/
theorem stack_alloc_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} {c : DataToWord.Config}
    {compile_rest : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)}
    {start : Nat} {anything : WordSemGcFun width}
    (hcode : ∀ k prog, sptLookup k s.code = some prog → k ≠ gcStubLocation ∧ StackProps.allocArg prog)
    (horacle : ∀ (i k : Nat) (q : HolProg width), (k, q) ∈ (s.compileOracle i).2.1 →
      k ≠ gcStubLocation ∧ StackProps.allocArg q)
    (hgc : s.gcFun = WordGcFunctions.wordGcFun c)
    (hbuf : s.bitmaps.length + s.dataBuffer.buffer.length + s.dataBuffer.spaceLeft < 2 ^ width - 1)
    (hst : s.stack.length * (width / 8) < 2 ^ width)
    (hK : s.useStack = true) (hA : s.useAlloc = true)
    (hC : s.compile = (fun cfg => compile_rest cfg ∘ List.map StackAlloc.progComp))
    (k : Nat) (r : Option (StackSemResult width)) (t : StackSemStateFiniteExact width C F)
    (he : StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { s with clock := k }) = (r, t))
    (hr : r ≠ some .error) :
    ∃ ck,
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with
          code := sptFromAList (StackAlloc.compile c (sptToAList s.code))
          gcFun := anything
          compile := compile_rest
          compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ s.compileOracle
          useStore := true, useStack := true, useAlloc := false, clock := k + ck })).1 = r ∧
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with
          code := sptFromAList (StackAlloc.compile c (sptToAList s.code))
          gcFun := anything
          compile := compile_rest
          compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ s.compileOracle
          useStore := true, useStack := true, useAlloc := false, clock := k + ck })).2.ffi = t.ffi := by
  obtain ⟨ck, regs1, he', -⟩ :=
    StackAlloc.comp_correct (anything := anything) (compile_rest := compile_rest)
      (.call none (.inl start) none) { s with clock := k } r t 0 0 c s.regs
      ⟨he, hr, ⟨trivial, trivial⟩, hcode, horacle, hgc, hA, hst, fun _ _ h => h, hK, hbuf, hC⟩
  exact ⟨ck, (congrArg Prod.fst he').trans rfl, (congrArg (fun p => p.2.ffi) he').trans rfl⟩

/-- Clocked `StackRemove` body simulation: at any clock `k`, a non-error entry call on `source`
produces a target run at clock `extra + k` with the exact same result and FFI state. -/
theorem stack_remove_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer start clock : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (relation : StackRemove.stateRelHOL jump bounds pointer source target)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), { source with clock := clock }) =
      (result, postSource))
    (nonError : result ≠ some .error) :
    ∃ extra postTarget,
      StackSemEvaluate.evaluate
        ((.call none (.inl start) none : HolProg width), { target with clock := extra + clock }) =
        (result, postTarget) ∧ postTarget.ffi = postSource.ffi :=
  StackRemove.CompileSemantics.entrySimulation jump bounds pointer start clock
    source target postSource result relation run nonError

/-- Clock-preserving `StackRemove` initializer shift: if `initCode` finishes normally
(`(none, t)`) from `s2`, then for every clock `k`, calling procedure `0` on `s2` at clock
`k + 1` produces the exact same result and FFI state as calling `start` on `t` at clock `k`. -/
theorem stack_remove_init_clocked_shift {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer start : Nat)
    (s2 t : StackSemStateFiniteExact width C F) (k : Nat)
    (hentry : sptLookup 0 s2.code =
      some (.seq (StackRemove.initCode generateGc maxHeap pointer)
        (.call none (.inl start) none)))
    (hrun : StackSemEvaluate.evaluate (StackRemove.initCode generateGc maxHeap pointer, s2) =
      (none, t)) :
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s2 with clock := k + 1 })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      { s2 with clock := k + 1 })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k })).2.ffi := by
  have clockRun := StackRemove.Proofs.InitClock.evaluateInitCodeClock
    generateGc maxHeap pointer s2 t none k hrun
  have body : StackSemEvaluate.evaluate
      (.seq (StackRemove.initCode generateGc maxHeap pointer) (.call none (.inl start) none),
        { s2 with clock := k }) =
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := k }) := by
    rw [StackSemEvaluate.evaluate_seq, clockRun]
    simp [StackSemControl.fixClock]
  have notBad := StackRemove.Proofs.InitSemantics.callNotBad start { t with clock := k }
  rw [StackSemEvaluate.evaluate_call]
  simp only [StackSemControl.findCode, hentry, Nat.add_one_ne_zero, if_false,
    StackSemStateOps.decClock, Nat.add_sub_cancel]
  rw [show ({ ({ s2 with clock := k + 1 } : StackSemStateFiniteExact width C F) with
      clock := k } : StackSemStateFiniteExact width C F) = { s2 with clock := k } from rfl, body]
  simp only [StackSemControl.fixClock, notBad]
  exact ⟨rfl, rfl⟩

/-- Clock-preserving `StackNames` simulation: at any clock `k`, calling `start` on
`renameState c f s` produces the exact same result and FFI state as calling `start` on `s`
at the same clock `k`. -/
theorem stack_names_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    {c : C → List (Nat × HolProg width) → Option (List (BitVec 8) × C)} {f : Spt Nat}
    {s : StackSemStateFiniteExact width C F}
    (hf : Function.Bijective (StackNames.findNameSpt f))
    (ha : ¬s.useAlloc) (hs : ¬s.useStore) (hk : ¬s.useStack)
    (hc : s.compile = (fun cfg => c cfg ∘ StackNames.compileHOL f))
    (start k : Nat) :
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { StackNames.renameState c f s with clock := k })).1 =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).1 ∧
    (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
      { StackNames.renameState c f s with clock := k })).2.ffi =
      (StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { s with clock := k })).2.ffi := by
  have h := StackNames.CompileSemantics.evaluate_entry_renameState
    (c := c) (f := f) (s := s) hf ha hs hk hc start k
  rw [h]
  exact ⟨rfl, rfl⟩

/-- Clocked `StackToLab` simulation: if a `StackSem` entry call at clock `k` finishes with
`FlattenSemantics.stackEntryClass res = .CompleteResult outcome`, then there exists `k'`
such that `LabSem.evaluate { s2 with clock := k + k' - 1 }` halts with `outcome` and the
same I/O events. -/
theorem stack_to_lab_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    {start : Nat}
    {s1 : StackSemStateFiniteExact width C F}
    {s2 : Flapjack.Compiler.Backend.LabSem.State width C F}
    (halt : FlattenCallCorrect.haltAssum C F s1.code)
    (rel : StateRel.stateRel s1 s2)
    (hpc : LabSem.locToPc start 0 s2.code = some s2.pc)
    (k : Nat) (outcome : HolOutcome) (ev : List HolIoEvent)
    (hrun : FlattenSemantics.stackRuns start s1 k = (.CompleteResult outcome, ev)) :
    ∃ k',
      (LabSem.evaluate { s2 with clock := k + k' - 1 }).1 = .halt outcome ∧
      (LabSem.evaluate { s2 with clock := k + k' - 1 }).2.ffi.ioEvents = ev := by
  have hne : (CrepToLoopSemanticsRunRes.CompleteResult outcome :
      CrepToLoopSemanticsRunRes HolOutcome) ≠ .RunError := by
    intro h
    cases h
  obtain ⟨k', hlab⟩ := FlattenSemantics.stackRunsSim halt rel hpc k
    (.CompleteResult outcome) ev hrun hne
  refine ⟨k', ?_⟩
  simp only [FlattenSemantics.labRuns] at hlab
  rcases he : LabSem.evaluate { s2 with clock := k + k' - 1 } with ⟨m, next⟩
  rw [he] at hlab
  simp only [Prod.map, Prod.mk.injEq] at hlab
  obtain ⟨hm, rfl⟩ := hlab
  cases m with
  | halt o =>
    simp only [FlattenSemantics.labEntryClass,
      CrepToLoopSemanticsRunRes.CompleteResult.injEq] at hm
    subst hm
    exact ⟨rfl, rfl⟩
  | error => simp [FlattenSemantics.labEntryClass] at hm
  | timeOut => simp [FlattenSemantics.labEntryClass] at hm

/-- Clocked `fullMakeInit` simulation (`StackToLab` + `StackNames` + `StackRemove` +
`StackAlloc` + `StackRawCall`): if `fullMakeInit` succeeds (`= (s, opt)`) under `Assumptions`,
then any non-error `StackSem` entry call on `s` at clock `k` finishing with
`FlattenSemantics.stackEntryClass res = .CompleteResult outcome` produces a `LabSem.evaluate`
run on `t` at some clock `k_lab` that halts with `outcome` and the same I/O events! -/
theorem full_make_init_clocked_halt {width : Nat} [NeZero width] {C F : Type}
    {stackConf : StackToLab.Config} {dataConf : DataToWord.Config} {maxHeap sp : Nat}
    {offset : BitVec width × BitVec width} {bitmaps : List (BitVec width)}
    {code : List (Nat × HolProg width)} {t : Flapjack.Compiler.Backend.LabSem.State width C F}
    {saveRegs : Nat → Bool} {dataSp : Nat}
    {coracle : Nat → C × List (Nat × HolProg width) × List (BitVec width)}
    {s : StackSemStateFiniteExact width C F}
    {opt : Option (StackSemStateFiniteExact width C F)}
    (hfm : FullMakeInit.fullMakeInit stackConf dataConf maxHeap sp offset bitmaps code t
      saveRegs dataSp coracle = (s, opt))
    (hA : Assumptions stackConf dataConf maxHeap sp offset bitmaps code t saveRegs dataSp coracle)
    (k : Nat) (res : Option (StackSemResult width)) (s_post : StackSemStateFiniteExact width C F)
    (outcome : HolOutcome)
    (hrun : StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        { s with clock := k }) = (res, s_post))
    (hclass : FlattenSemantics.stackEntryClass res = .CompleteResult outcome) :
    ∃ k_lab,
      (LabSem.evaluate { t with clock := k_lab }).1 = .halt outcome ∧
      (LabSem.evaluate { t with clock := k_lab }).2.ffi.ioEvents = s_post.ffi.ioEvents := by
  have hne : res ≠ some .error := by
    rintro rfl
    simp [FlattenSemantics.stackEntryClass] at hclass
  rw [fullMakeInit_eq] at hfm
  simp only [Prod.mk.injEq] at hfm
  obtain ⟨rfl, rfl⟩ := hfm
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hgood, hgoodO, -, -, -, -, -, -, -, -⟩ := id hA
  have hdis := dischargeThese_s2 hA
  have hprop2 := propagateThese_s2 hA
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := And.intro hdis hprop2
  have codeRel : StackRemove.codeRelHOL stackConf.jump offset sp
      (sptFromAList (code1 dataConf code))
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).code :=
    StackRemove.Proofs.InitCodeRelation.impCodeRel stackConf.jump offset
      (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
      (code1 dataConf code) _ ⟨every, codeEq⟩
  have errLab : sptLookup StackRemove.stackErrLab
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle).code =
      some (StackRemove.haltInst (BitVec.ofNat width 2)) := by
    rw [codeEq, sptLookup_sptFromAList]
    simp [StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup, StackRemove.stackErrLab]
  have pre : StackRemove.Proofs.InitMake.initPre (StackToLab.isGenGc dataConf.gcKind) maxHeap
      bitmaps dataSp sp BvlToBvi.initGlobalsLocation
      (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) := by
    refine ⟨?_, ?_, maxOk⟩
    · rw [codeEq, sptLookup_sptFromAList]
      simp [StackRemove.compileHOL, StackRemove.initStubs, sptAListLookup]
    · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
        rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
      rw [sub] at heap
      exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
        m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  have hinit := StackRemove.Proofs.InitSemantics.evaluateInitCode
    (StackToLab.isGenGc dataConf.gcKind) maxHeap bitmaps dataSp sp BvlToBvi.initGlobalsLocation
    (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
    stackConf.jump offset (coracle1 coracle) (sptFromAList (code1 dataConf code))
    ⟨pre, oracleEq, oracleBound, errLab, codeRel⟩
  revert hinit
  cases hinitRun : StackSemEvaluate.evaluate
      (StackRemove.initCode (StackToLab.isGenGc dataConf.gcKind) maxHeap sp,
        s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) with
  | mk initRes t_rem =>
    cases initRes with
    | some _ => intro h; exact False.elim h
    | none =>
      rintro ⟨s1, hopt, rel_rem, _⟩
      have hs1 : StackRemove.Proofs.InitMake.makeInitAny (StackToLab.isGenGc dataConf.gcKind)
          maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
          (sptFromAList (code1 dataConf code))
          (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) = s1 := by
        unfold StackRemove.Proofs.InitMake.makeInitAny
        rw [hopt]
      rw [hs1] at hrun
      obtain ⟨post, hpost, hprop⟩ := StackRemove.Proofs.InitAny.makeInitOpt_eq_some hopt
      -- Step 1: StackRawCall simulation from `s` (`makeInit dataConf (sptFromAList code) coracle s1`)
      obtain ⟨ck1, t_rc, hrun_rc, hffi_rc⟩ := stack_rawcall_clocked_sim code
        (StackAlloc.makeInit dataConf (sptFromAList code) coracle s1)
        BvlToBvi.initGlobalsLocation k res s_post hgood.1 rfl hrun hne
      have hm : { StackAlloc.makeInit dataConf (sptFromAList code) coracle s1 with
          code := sptFromAList (StackRawCall.compile code), clock := k + ck1 } =
          { StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1 with
            clock := k + ck1 } := by
        simp [StackAlloc.makeInit]
      rw [hm] at hrun_rc
      -- Step 2: StackAlloc simulation to `s1`
      have hu := StackRemove.Proofs.InitAny.makeInitAnyUseStack (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hus := StackRemove.Proofs.InitAny.makeInitAnyUseStore (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hua := StackRemove.Proofs.InitAny.makeInitAnyUseAlloc (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hcd := StackRemove.Proofs.InitAny.makeInitAnyCode (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      have hco := StackRemove.Proofs.InitAny.makeInitAnyCompileOracle
        (StackToLab.isGenGc dataConf.gcKind)
        maxHeap bitmaps dataSp (coracle1 coracle) stackConf.jump offset sp
        (sptFromAList (code1 dataConf code))
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
      rw [hs1] at hu hus hua hcd hco
      have hcode_sa : ∀ k prog,
          sptLookup k (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).code = some prog →
          k ≠ gcStubLocation ∧ StackProps.allocArg prog := by
        intro k0 prog hk0
        simp only [StackAlloc.makeInit, sptLookup_sptFromAList] at hk0
        obtain ⟨⟨n0, p0⟩, hm0, he⟩ := List.mem_map.mp (sptAListLookup_mem hk0)
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨hst, hal⟩ := hgood.2.1 _ hm0
        exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega,
          (StackRawCall.callArgComp _ _).2.mpr hal⟩
      have horacle_sa : ∀ (i k : Nat) (q : HolProg width),
          (k, q) ∈ ((StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).compileOracle i).2.1 →
          k ≠ gcStubLocation ∧ StackProps.allocArg q := by
        intro i k0 q hq
        obtain ⟨hst, hal⟩ := (hgoodO i).2.1 _ hq
        exact ⟨by simp only [stackNumStubs, gcStubLocation] at hst ⊢; omega, hal⟩
      have hbuf_sa : (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).bitmaps.length +
          (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).dataBuffer.buffer.length +
          (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).dataBuffer.spaceLeft <
          2 ^ width - 1 := by
        subst hpost
        rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          hdb, _, _, _, hbl, _⟩
        simp only [StackAlloc.makeInit, StackRemove.Proofs.InitReduce.initReduce] at hbl hdb ⊢
        simp only [List.length_nil, Nat.add_zero]
        omega
      have hst_sa : (StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1).stack.length *
          (width / 8) < 2 ^ width := by
        subst hpost
        rcases hprop with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
          _, _, _, _, _, _, _, hsb, _⟩
        exact hsb
      have hnodup_rc : ((StackRawCall.compile code).map Prod.fst).Nodup := by
        rw [StackRawCall.mapFstCompile]; exact hgood.1
      obtain ⟨ck2, hrun_sa1, hffi_sa⟩ := stack_alloc_clocked_sim
        (s := StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1)
        (c := dataConf) (compile_rest := s1.compile) (start := BvlToBvi.initGlobalsLocation)
        (anything := s1.gcFun)
        hcode_sa horacle_sa rfl hbuf_sa hst_sa rfl rfl rfl (k + ck1) res t_rc hrun_rc hne
      let m_sa := StackAlloc.makeInit dataConf (sptFromAList (StackRawCall.compile code)) coracle s1
      have hs1_eq : { m_sa with
          code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
          gcFun := s1.gcFun
          compile := s1.compile
          compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
          useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 } =
          { s1 with clock := k + ck1 + ck2 } := by
        have hcc : sptFromAList (StackAlloc.compile dataConf
            (sptToAList (sptFromAList (StackRawCall.compile code)))) = s1.code := by
          rw [hcd, code1]
          refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
          rw [StackAlloc.CompCorrect.sptLookup_compile, StackAlloc.CompCorrect.sptLookup_compile,
            StackAlloc.ProgCompSupport.sptAListLookup_sptToAList, sptLookup_sptFromAList]
        cases s1
        simp only [m_sa, StackAlloc.makeInit, coracle1] at hcc hco hus hu hua ⊢
        simp only [Bool.not_eq_true] at hua
        subst hus hu hua
        rw [hcc, hco]
      change (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { m_sa with
            code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
            gcFun := s1.gcFun
            compile := s1.compile
            compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
            useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 })).1 = res at hrun_sa1
      change (StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { m_sa with
            code := sptFromAList (StackAlloc.compile dataConf (sptToAList m_sa.code))
            gcFun := s1.gcFun
            compile := s1.compile
            compileOracle := Prod.map id (Prod.map (List.map StackAlloc.progComp) id) ∘ m_sa.compileOracle
            useStore := true, useStack := true, useAlloc := false, clock := k + ck1 + ck2 })).2.ffi = t_rc.ffi at hffi_sa
      rw [hs1_eq] at hrun_sa1 hffi_sa
      rcases hrun_s1 : StackSemEvaluate.evaluate
        ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
          { s1 with clock := k + ck1 + ck2 }) with ⟨res_s1, post_s1⟩
      rw [hrun_s1] at hrun_sa1 hffi_sa
      simp only at hrun_sa1 hffi_sa
      subst res_s1
      -- Step 3: StackRemove body simulation from `s1` to `t_rem`
      obtain ⟨ck3, post_rem, hrun_rem, hffi_rem⟩ := stack_remove_clocked_sim
        stackConf.jump offset sp BvlToBvi.initGlobalsLocation (k + ck1 + ck2)
        s1 t_rem post_s1 res rel_rem hrun_s1 hne
      -- Step 4: StackRemove initCode shift (+1) from `t_rem` at `BvlToBvi.initGlobalsLocation` to `s2` at `0`
      have hshift := stack_remove_init_clocked_shift
        (StackToLab.isGenGc dataConf.gcKind) maxHeap sp BvlToBvi.initGlobalsLocation
        (s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle) t_rem
        (ck3 + (k + ck1 + ck2)) pre.1 hinitRun
      -- Step 5: StackNames agreement from `s2` to `s3` at `0`
      let s3_st := s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle
      let s2_st := s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle
      have hbij := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have hnames := stack_names_clocked_agree
        (c := s3_st.compile)
        (f := stackConf.regNames)
        (s := s2_st)
        hbij
        (by simp [s2_st, noAlloc])
        (by simp [s2_st, noStore])
        (by simp [s2_st, noStack])
        rfl 0 (ck3 + (k + ck1 + ck2) + 1)
      have hs3_def : StackNames.renameState s3_st.compile stackConf.regNames s2_st = s3_st := by
        have hinv : ∀ y, StackNames.findNameSpt stackConf.regNames
            (holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) y) = y :=
          apply_holLinv_of_surjective hbij.2
        have hc : sptFromAList (StackNames.compileHOL stackConf.regNames
            (sptToAList (sptFromAList (code2 stackConf dataConf maxHeap sp offset code)))) =
            s3_st.code := by
          change _ = sptFromAList (StackNames.compileHOL stackConf.regNames
            (code2 stackConf dataConf maxHeap sp offset code))
          refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
          rw [sptLookup_sptFromAList, StackNames.sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
            sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, sptLookup_sptFromAList,
            StackNames.sptAListLookup_compileHOL]
        classical
        have hsave : (fun y => decide (∃ x, decide (∃ z, s3_st.ffiSaveRegs z = true ∧
            x = holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) z) = true ∧
            y = StackNames.findNameSpt stackConf.regNames x)) = s3_st.ffiSaveRegs := by
          funext y
          by_cases hy : s3_st.ffiSaveRegs y = true
          · rw [hy, decide_eq_true_iff]
            exact ⟨holLinv (StackNames.findNameSpt stackConf.regNames) (fun _ => True) y,
              decide_eq_true_iff.mpr ⟨y, hy, rfl⟩, (hinv y).symm⟩
          · rw [Bool.not_eq_true] at hy
            rw [hy, decide_eq_false_iff_not]
            rintro ⟨x, hx, rfl⟩
            obtain ⟨z, hz, rfl⟩ := decide_eq_true_iff.mp hx
            rw [hinv z, hz] at hy
            exact Bool.noConfusion hy
        have hor : s3_st.compileOracle =
            Prod.map id (Prod.map (StackNames.compileHOL stackConf.regNames) id) ∘
              coracle2 stackConf sp offset coracle := rfl
        simp only [s2_st, s2, StackNames.renameState, StackNames.makeInit,
          StackNames.MakeInit.mapKeys_mapKeys_linv hbij, hc, ← hor]
        refine Eq.trans ?_ (show { s3_st with ffiSaveRegs := s3_st.ffiSaveRegs } = s3_st from rfl)
        congr 1
      rw [hs3_def] at hnames
      -- Step 6: StackToLab simulation from `s3` at `0` to `t`
      have hruns_s3 : FlattenSemantics.stackRuns 0
          (s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle)
          (ck3 + (k + ck1 + ck2) + 1) =
          (.CompleteResult outcome, s_post.ffi.ioEvents) := by
        simp only [FlattenSemantics.stackRuns, Prod.map]
        rcases hev_s3 : StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 }) with ⟨r_s3, p_s3⟩
        have hnames1 := hnames.1
        change (StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 })).1 =
          (StackSemEvaluate.evaluate
            ((.call none (.inl 0) none : HolProg width),
              { s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
                clock := ck3 + (k + ck1 + ck2) + 1 })).1 at hnames1
        have hnames2 := hnames.2
        change (StackSemEvaluate.evaluate
          ((.call none (.inl 0) none : HolProg width),
            { s3 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
              clock := ck3 + (k + ck1 + ck2) + 1 })).2.ffi =
          (StackSemEvaluate.evaluate
            ((.call none (.inl 0) none : HolProg width),
              { s2 stackConf dataConf maxHeap sp offset code t saveRegs coracle with
                clock := ck3 + (k + ck1 + ck2) + 1 })).2.ffi at hnames2
        have hr_eq : r_s3 = res := by
          rw [hev_s3, hshift.1, hrun_rem] at hnames1
          exact hnames1
        have hffi_eq : p_s3.ffi = s_post.ffi := by
          rw [hev_s3, hshift.2, hrun_rem] at hnames2
          exact hnames2.trans (hffi_rem.trans (hffi_sa.trans hffi_rc))
        rw [hr_eq, hclass, hffi_eq]
      obtain ⟨k', hhalt, hev_lab⟩ := stack_to_lab_clocked_halt
        MakeInit.haltAssumLemma (stateRel_s3 hA) (locToPc_start hA)
        (ck3 + (k + ck1 + ck2) + 1) outcome s_post.ffi.ioEvents hruns_s3
      exact ⟨(ck3 + (k + ck1 + ck2) + 1) + k' - 1, hhalt, hev_lab⟩

private theorem sptAListLookup_eq_local {α : Type} (key : Nat) :
    ∀ entries : List (Nat × α), sptAListLookup key entries = panPropsALookupEq key entries
  | [] => rfl
  | (other, value) :: entries => by
      simp only [sptAListLookup, panPropsALookupEq, sptAListLookup_eq_local key entries]
      by_cases h : key = other
      · subst h; simp
      · simp [h, Ne.symm h]

private theorem mem_of_lookup_local {α : Type} {key : Nat} {value : α} :
    ∀ {entries : List (Nat × α)}, panPropsALookupEq key entries = some value →
      (key, value) ∈ entries
  | [], h => by simp [panPropsALookupEq] at h
  | (other, v) :: entries, h => by
      simp only [panPropsALookupEq] at h
      by_cases ho : other = key
      · subst ho
        simp only [decide_true, if_true, Option.some.injEq] at h
        subst h
        exact List.mem_cons_self
      · simp only [ho, decide_false, Bool.false_eq_true, if_false] at h
        exact List.mem_cons_of_mem _ (mem_of_lookup_local h)

/-- Top-level `WordToStack.Native` clocked simulation under `wordLangSafeForSpace`:
from `initStateOk` and the `compileNative` conventions, a non-error `WordSem` entry call
on `makeInit asmConf k t (sptFromAList code) coracle` at clock `clk` yields a `StackSem`
entry call on `t` at clock `clk + ck` with mapped result and identical FFI state. -/
theorem word_to_stack_compile_clocked_sim {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (start clk : Nat)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (codeEq : t.code = sptFromAList (WordToStack.Native.compileNative asmConf false code).2.2.2)
    (kEq : k = asmConf.regCount - (5 + asmConf.avoidRegs.length))
    (ok : WordToStackProofs.InitializationStateRel.initStateOk asmConf k t coracle)
    (noRaise : panPropsALookupEq raiseStubLocation code = none)
    (noStore : panPropsALookupEq storeConstsStubLocation code = none)
    (bitmapsPrefix : (WordToStack.Native.compileNative asmConf false code).1 <+: t.bitmaps)
    (conventions : ∀ entry ∈ code, flatExpConventions entry.2.2 = true ∧
      postAllocConventionsHOL (asmConf.regCount - (5 + asmConf.avoidRegs.length))
        entry.2.2 = true)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace
      (WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle) start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { WordToStack.Native.Initialization.makeInit asmConf k t (sptFromAList code) coracle with
        clock := clk } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ ck t1,
      StackSemEvaluate.evaluate ((.call none (.inl start) none : HolProg width),
        { t with clock := clk + ck }) =
        (res.map WordToStackProofs.CompCorrect.compileResult, t1) ∧
      s1.ffi = t1.ffi := by
  subst kEq
  rcases compiled : WordToStack.Native.compileWordToStackNative asmConf false
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) code (.list [4], 1) with
    ⟨bodies, frames, output, nextIndex⟩
  simp only [WordToStack.Native.compileNative, Bool.false_eq_true, if_false, compiled]
    at codeEq bitmapsPrefix
  have keys := Flapjack.WordToStackProofs.mapFstCompileWordToStack asmConf false _ code (.list [4], 1)
    bodies (frames, (output, nextIndex)) compiled
  have stubsDistinct : raiseStubLocation ≠ storeConstsStubLocation := by
    simp [raiseStubLocation, storeConstsStubLocation, wordNumStubs]
  have related : WordToStackProofs.stateRel asmConf
      (asmConf.regCount - (5 + asmConf.avoidRegs.length)) 0 0
      (WordToStack.Native.Initialization.makeInit asmConf
        (asmConf.regCount - (5 + asmConf.avoidRegs.length)) t (sptFromAList code)
        coracle : WordSemStateFiniteExact width (Nat × C) F)
      t [] 0 := by
    apply WordToStackProofs.InitializationStateRel.initStateOkImpliesStateRel
    refine ⟨?_, ?_, ?_, ?_, ok⟩
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
      simp [panPropsALookupEq]
    · rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
      simp [panPropsALookupEq, stubsDistinct]
    · intro n wordProg argumentCount lookup
      rw [sptLookup_sptFromAList, sptAListLookup_eq_local] at lookup
      have member := mem_of_lookup_local lookup
      obtain ⟨flat, allocated⟩ := conventions _ member
      obtain ⟨bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, bodyLookup⟩ :=
        WordToStack.Native.compileWordToStackImpALookup asmConf false _ code (.list [4]) 1
          bodies frames output nextIndex n argumentCount wordProg t.bitmaps compiled lookup
          (by simp [appListAppend, appendAux]) (by simp [appListAppend, appendAux])
          (by simpa [appListAppend, appendAux] using bitmapsPrefix)
      refine ⟨allocated, flat, bs, i, bs2, i2, frame, body, compileRun, b1, b2, b3, ?_⟩
      have notRaise : n ≠ raiseStubLocation := by
        rintro rfl
        rw [noRaise] at lookup
        cases lookup
      have notStore : n ≠ storeConstsStubLocation := by
        rintro rfl
        rw [noStore] at lookup
        cases lookup
      rw [codeEq, sptLookup_sptFromAList, sptAListLookup_eq_local]
      simp [panPropsALookupEq, Ne.symm notRaise, Ne.symm notStore, bodyLookup]
    · rw [codeEq, sptDomainFromAList, sptDomainFromAList]
      funext x
      simp only [List.map_cons, List.mem_cons, keys]
  exact word_to_stack_clocked_sim asmConf (asmConf.regCount - (5 + asmConf.avoidRegs.length))
    _ t start clk res s1 related safe hrun hne

#print axioms word_to_word_clocked_agree
#print axioms word_to_stack_clocked_sim
#print axioms stack_rawcall_clocked_sim
#print axioms stack_alloc_clocked_sim
#print axioms stack_remove_clocked_sim
#print axioms stack_remove_init_clocked_shift
#print axioms stack_names_clocked_agree
#print axioms stack_to_lab_clocked_halt
#print axioms full_make_init_clocked_halt
#print axioms word_to_stack_compile_clocked_sim

end InitE
