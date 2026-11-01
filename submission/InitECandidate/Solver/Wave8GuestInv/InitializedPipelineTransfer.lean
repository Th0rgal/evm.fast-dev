import InitECandidate.Solver.Wave8GuestInv.EntryClassTransfer
import InitECandidate.Solver.Wave8Stage.FrontendStaticBudget

/-! Successful initialization: compose the actual frontend, WordToWord,
WordToStack simulations. The frontend relation and FullMakeInit
assumptions remain explicit. No intermediate evaluator run is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer
open Classical InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs
open Flapjack.Pancake.Proofs.PanToTarget Flapjack.LoopToWord.CompileCorrect
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenSemantics
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.SelfContainedStageBounds
open EntryClassTransfer

/-- The original frontend simulation relation, without an execution premise. -/
def FrontendRelation {width : Nat} [NeZero width] {C F : Type}
    (source : PanSemStateFiniteExact width F) (target : WordSemStateFiniteExact width C F)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width) : Prop :=
(∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
      noLabelsHOL target.memory (fun address => target.mdomain address = true) ∧
      start = ofString "main" ∧
      globalsSize = ((decShapesHOL code).map
        (sizeOfShapeWithContextHOL (holThe (decsStcnamesHOLExact [] code)))).sum ∧
      distinctParamsHOL (functionsHOL code) ∧
      (fun address => target.mdomain address = true) =
        (fun address => source.memaddrs address ∨ Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address) ∧
      (fun address => target.shMdomain address = true) = source.shMemaddrs ∧
      target.be = source.be ∧ target.ffi = source.ffi ∧
      target.store.lookup .currHeap = some (.word source.baseAddr) ∧
      target.store.lookup .heapLength = some (.word heapLen) ∧
      source.topAddr = source.baseAddr + (2 : BitVec width) * heapLen - panBytesInWord width * BitVec.ofNat width globalsSize ∧
      ((functionsHOL code).map Prod.fst).Nodup ∧ panGlobalsByteAlignedHOL source.topAddr ∧
      globalsAllocatableHOL source code ∧ source.code = HolFiniteMapExact.empty ∧
      target.code = sptFromAList (panToWordCompileProgHOL arch code) ∧
      source.globals = HolFiniteMapExact.empty ∧ source.locals = HolFiniteMapExact.empty ∧
      sizeOfEidsHOL code < 2 ^ width ∧ source.eshapes = HolFiniteMapExact.empty ∧
      sptLookup 0 target.locals = some (WordLocW.loc 1 0) ∧ goodDimindex width ∧
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail

abbrev nativeWordState {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width)
    (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (stack : StackSemStateFiniteExact width C F) (cfg : C) :=
  WordToStack.Native.Initialization.makeInit ac
    (ac.regCount - (5 + ac.avoidRegs.length)) stack (sptFromAList code)
    (fun _ => ((bitmaps.length,cfg), []))

/-- Preserve all fields, including stackSize computed from allocated code. -/
abbrev frontendWordState {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (panCode : List (DeclHOL width))
    (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (stack : StackSemStateFiniteExact width C F) (cfg : C) :=
  {nativeWordState ac code bitmaps stack cfg with
    code := sptFromAList (panToWordCompileProgHOL ac.isa panCode)}

noncomputable def wordClock {width : Nat} [NeZero width]
    (panCode : List (DeclHOL width)) (start : MlS) (k : Nat) : Nat :=
  (FrontendStaticBudget.staticFrontBudget panCode start + 1) * k +
    (FrontendStaticBudget.staticFrontBudget panCode start + 4)

noncomputable def stackClock {width : Nat} [NeZero width]
    (panCode : List (DeclHOL width)) (start : MlS)
    (code : List (Nat × Nat × WordLangProgHOL (BitVec width))) (k : Nat) : Nat :=
  (WordToStackStaticBudget.codeBudget (sptFromAList code) + 1) * wordClock panCode start k

/-- A complete Stack entry at the actual compiled and initialized state.
The frontend coefficient uses the deterministic association-list budget. -/
theorem pan_to_initialized_stack_complete {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (wc : WordToWord.Config) (panCode : List (DeclHOL width))
    (col : List (Option (Spt Nat)))
    (wordCode : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (bitmaps : List (BitVec width)) (wconf : WordToStack.Native.Config) (fs : List Nat)
    (stackCode : List (Nat × HolProg width))
    (scc : StackToLab.Config) (dc : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (lab : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat) (cfg : C)
    (stack aux : StackSemStateFiniteExact width C F)
    (dimension : goodDimindex width) (registers : ac.avoidRegs.length + 13 ≤ ac.regCount)
    (isa : ac.isa ≠ .ag32)
    (wtw : WordToWord.compile wc ac (panToWordCompileProgHOL ac.isa panCode) = (col,wordCode))
    (wts : WordToStack.Native.compileNative ac false wordCode = (bitmaps,wconf,fs,stackCode))
    (initialized : FullMakeInit.fullMakeInit scc dc maxHeap sp offset bitmaps stackCode lab
      saveRegs dataSp (fun _ => (cfg, [], [])) = (stack, some aux))
    (source : PanSemStateFiniteExact width F) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (front : FrontendRelation source (frontendWordState ac panCode wordCode bitmaps stack cfg)
      ac.isa panCode start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width F)
    (hst : decsStcnamesHOLExact [] panCode = some stCtxt)
    (decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width F _
      {source with structs := stCtxt} (fun a => Classical.propDecidable (source.memaddrs a))
      panCode = some s_decls)
    (k : Nat) (result : Option (PanSemResultExact width))
    (post : PanSemStateFiniteExact width F)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {s_decls with clock := k}
      (.call none start [] : ProgHOL width) = (result,post))
    (notError : panEntryClass result ≠ .RunError)
    (notTimeout : result ≠ some .timeOut) :
    ∃ outcome, stackEntryClass (StackSemEvaluate.evaluate
      ((.call none (.inl BvlToBvi.initGlobalsLocation) none : HolProg width),
        {stack with clock := stackClock panCode start wordCode k})).1 = .CompleteResult outcome := by
  let pre := frontendWordState ac panCode wordCode bitmaps stack cfg
  let oldClock := (FrontendCostTransfer.frontBudget panCode start + 1) * k +
    (FrontendCostTransfer.frontBudget panCode start + 4)
  have oldClass := FrontendStackTransfer.pan_to_word_static_class source pre ac.isa panCode
    start globalsSize heapLen front stCtxt s_decls hst decls k result post run notError notTimeout
  have sourceComplete : ∃ outcome, panEntryClass result = .CompleteResult outcome := by
    cases result with
    | none => exact False.elim (notError rfl)
    | some r => cases r <;> simp_all [panEntryClass]
  have oldComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock}).1 =
        .CompleteResult outcome := by
    rw [oldClass]
    exact sourceComplete
  have oldNotTimeout : (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock}).1 ≠ some .timeOut := by
    obtain ⟨outcome,complete⟩ := oldComplete
    intro bad
    rw [bad] at complete
    cases complete
  have frontBound := FrontendStaticBudget.frontBudget_le_staticFrontBudget panCode start
  have enough : oldClock ≤ wordClock panCode start k :=
    Nat.add_le_add (Nat.mul_le_mul_right k (Nat.add_le_add_right frontBound 1))
      (Nat.add_le_add_right frontBound 4)
  rcases oldRun : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := oldClock} with ⟨r,t⟩
  have lift := WordSemStateFiniteExact.evaluate_add_clock (wordClock panCode start k-oldClock)
    (.call none (some firstLoopName) [0] none) {pre with clock := oldClock} r t
    ⟨oldRun,by rw [oldRun] at oldNotTimeout; exact oldNotTimeout⟩
  have clockEq : oldClock+(wordClock panCode start k-oldClock) = wordClock panCode start k :=
    Nat.add_sub_of_le enough
  simp only [clockEq] at lift
  have preComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := wordClock panCode start k}).1 =
        .CompleteResult outcome := by
    rw [lift]
    rw [oldRun] at oldComplete
    exact oldComplete
  have preNotError : (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none) {pre with clock := wordClock panCode start k}).1 ≠
        some .error := by
    obtain ⟨outcome,complete⟩ := preComplete
    intro bad
    rw [bad] at complete
    cases complete
  have facts := panToTargetWordStateFacts ac (ac.regCount - (5 + ac.avoidRegs.length))
    (sptFromAList wordCode) (fun _ => ((bitmaps.length,cfg), [])) scc dc maxHeap sp
    offset bitmaps stackCode lab saveRegs dataSp (fun _ => (cfg, [], [])) stack aux initialized
  have agree := word_to_word_clocked_agree wc ac (panToWordCompileProgHOL ac.isa panCode)
    col wordCode pre firstLoopName (wordClock panCode start k) wtw facts.1
    (PanToWord.pan_to_word_compile_prog_no_install_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_alloc_code _ panCode _ rfl)
    (PanToWord.pan_to_word_compile_prog_no_mt_code _ panCode _ rfl) rfl rfl preNotError
  have allocatedComplete : ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none)
      {nativeWordState ac wordCode bitmaps stack cfg with clock := wordClock panCode start k}).1 =
        .CompleteResult outcome := by
    change ∃ outcome, wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none)
      {pre with clock := wordClock panCode start k, code := sptFromAList wordCode}).1 = _
    rw [agree.1]
    exact preComplete
  exact initialized_word_to_stack_complete ac wc panCode col wordCode bitmaps wconf fs stackCode
    scc dc maxHeap sp offset lab saveRegs dataSp cfg stack aux firstLoopName
    (wordClock panCode start k) dimension registers isa wtw wts initialized allocatedComplete

end InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer
