import InitECandidate.Solver.Wave8Stage.FrontendCostTransfer
import InitECandidate.Solver.Wave8Stage.WordToStackStaticBudget

/-! Compose the verified frontend and WordToStack simulations at their static
budgets. Every initial-state relation remains explicit; the Word non-error
premise is derived from source result preservation, rather than assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8GuestInv.FrontendStackTransfer
open Classical InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.LoopToWord.CompileCorrect
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.Wave8Stage
open FrontendCostTransfer

/-- The static frontend budget preserves both the non-error and non-timeout
facts needed by the next actual compiler simulation. -/
theorem pan_to_word_static_class {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
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
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (hnt_src : res_src ≠ some .timeOut) :
    LoopToWordStateRelImpSemanticsSupport.wordEntryClass
      (WordSemStateFiniteExact.evaluate
        (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
        {target with clock := (frontBudget code start + 1) * k + (frontBudget code start + 4)}).1 =
      panEntryClass res_src := by
  obtain ⟨extra,post,result,run,_,hclass,hbound⟩ :=
    FrontendCostTransfer.pan_to_word_clocked_sim source target arch code start globalsSize heapLen h
      stCtxt s_decls hst hev_decls k res_src s_src_post hev_call hne_src
  have hnt : result ≠ some .timeOut := by
    intro bad
    rw [bad] at hclass
    cases res_src with
    | none => cases hclass
    | some r =>
      cases r <;> simp_all [LoopToWordStateRelImpSemanticsSupport.wordEntryClass, panEntryClass]
  let budget := (frontBudget code start + 1) * k + (frontBudget code start + 4)
  have enough : (k+1)+extra ≤ budget := by
    dsimp only [budget]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hbound ⊢
    omega
  have lifted := WordSemStateFiniteExact.evaluate_add_clock (budget-((k+1)+extra))
    (.call none (some firstLoopName) [0] none)
    {target with clock := (k+1)+extra} result post ⟨run,hnt⟩
  have eqClock : (k+1)+extra+(budget-((k+1)+extra)) = budget := by omega
  simp only [eqClock] at lifted
  change LoopToWordStateRelImpSemanticsSupport.wordEntryClass
    (WordSemStateFiniteExact.evaluate _ {target with clock := budget}).1 = panEntryClass res_src
  rw [lifted]
  exact hclass

theorem pan_to_word_static_result {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
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
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (hnt_src : res_src ≠ some .timeOut) :
    (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      {target with clock := (frontBudget code start + 1) * k + (frontBudget code start + 4)}).1 ≠ some .error ∧
    (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      {target with clock := (frontBudget code start + 1) * k + (frontBudget code start + 4)}).1 ≠ some .timeOut := by
  obtain ⟨extra,post,result,run,_,hclass,hbound⟩ :=
    FrontendCostTransfer.pan_to_word_clocked_sim source target arch code start globalsSize heapLen h
      stCtxt s_decls hst hev_decls k res_src s_src_post hev_call hne_src
  have hne : result ≠ some .error := by
    intro bad
    rw [bad] at hclass
    exact hne_src hclass.symm
  have hnt : result ≠ some .timeOut := by
    intro bad
    rw [bad] at hclass
    cases res_src with
    | none => cases hclass
    | some r =>
      cases r <;> simp_all [LoopToWordStateRelImpSemanticsSupport.wordEntryClass, panEntryClass]
  let budget := (frontBudget code start + 1) * k + (frontBudget code start + 4)
  have enough : (k+1)+extra ≤ budget := by
    dsimp only [budget]
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one] at hbound ⊢
    omega
  have lifted := WordSemStateFiniteExact.evaluate_add_clock (budget-((k+1)+extra))
    (.call none (some firstLoopName) [0] none)
    {target with clock := (k+1)+extra} result post ⟨run,hnt⟩
  have eqClock : (k+1)+extra+(budget-((k+1)+extra)) = budget := by omega
  simp only [eqClock] at lifted
  change (WordSemStateFiniteExact.evaluate _ {target with clock := budget}).1 ≠ _ ∧
    (WordSemStateFiniteExact.evaluate _ {target with clock := budget}).1 ≠ _
  rw [lifted]
  exact ⟨hne,hnt⟩

/-- Actual Pan-to-Stack non-timeout from the Pan source run, the frontend
initial relation, and WordToStack's original relation and no-install premise.
No Word or Stack execution hypothesis is added. -/
theorem pan_to_stack_static_not_timeOut {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width (Nat × C) σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (ac : AsmConfigExact width) (registers : Nat)
    (stack : StackSemStateFiniteExact width C σ)
    (related : WordToStackProofs.stateRel ac registers 0 0 target stack [] 0)
    (noInstall : WordProps.noInstallCode target.code)
    (h : (∀ address, source.memaddrs address → target.memory address = wlabWlocExact (source.memory address)) ∧
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
      PanSemStateFiniteExact.semanticsDecls source start code ≠ .fail)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k : Nat) (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (hnt_src : res_src ≠ some .timeOut) :
    let wordClock := (frontBudget code start + 1) * k + (frontBudget code start + 4)
    (StackSemEvaluate.evaluate
      ((.call none (.inl firstLoopName) none : Compiler.Backend.StackLang.HolProg width),
        {stack with clock := (WordToStackStaticBudget.codeBudget target.code + 1) * wordClock})).1 ≠
      some .timeOut := by
  intro wordClock
  obtain ⟨hne,hnt⟩ := pan_to_word_static_result source target arch code start globalsSize heapLen h
    stCtxt s_decls hst hev_decls k res_src s_src_post hev_call hne_src hnt_src
  exact WordToStackStaticBudget.notTimeOutOfStaticBudget ac firstLoopName registers wordClock
    target stack related noInstall hne hnt

end InitECandidate.Solver.Wave8GuestInv.FrontendStackTransfer
