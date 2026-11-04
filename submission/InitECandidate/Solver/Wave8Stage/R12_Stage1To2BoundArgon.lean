import InitE.SourceCodeFacts
import InitECandidate.Solver.Wave8Stage.FrontendStaticBudget
import InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrep
import InitECandidate.Solver.Wave8Stage.ConcreteFrontendState
import InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.R12_Stage1To2BoundArgon

open Classical
open InitE
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.LoopToWordStateRelImpSemanticsSupport
open InitECandidate.Proofs
open InitECandidate.Solver.FastEnv
open InitECandidate.Solver.SelfContainedStageBounds
open InitECandidate.Solver.Wave8Stage.CrepSourceCostBound
open InitECandidate.Solver.Wave8Stage.FrontendCostTransfer
open InitECandidate.Solver.Wave8Stage.FrontendStaticBudget
open InitECandidate.Solver.Wave8GuestInv.FrontendStackTransfer
open InitECandidate.Solver.Wave8GuestInv.InitializedPipelineTransfer

/-- Certified factor-two Stack clock budget `2 * wordClock panCode start clock`. -/
noncomputable def certifiedStackClock {width : Nat} [NeZero width]
    (panCode : List (DeclHOL width)) (start : MlS) (clock : Nat) : Nat :=
  2 * wordClock panCode start clock

/-- Reduction of the concrete Crep compilation stage on `sourceDeclarations` and `"main"`
to the pre-certified `ConcreteCompilerCrep.source` declaration list. -/
theorem compileProgDeclsHOLW_sourceDeclarations_eq :
    compileProgDeclsHOLW
      (compileTopExactHOL
        (Pancake.PanStructs.CompileShapeExact.compileTopExact
          (panSimpDeclsHOL sourceDeclarations))
        (ofString "main")) = ConcreteCompilerCrep.source := by
  rw [ConcreteCompilerSource.source_eq, ConcreteCompilerSimp.source_eq,
    ConcreteCompilerStruct.source_eq, ConcreteCompilerGlobals.compile_eq,
    ConcreteCompilerCrep.source_eq]

/-- `staticFrontBudget` on `sourceDeclarations` and `"main"` equals `listBudget ConcreteCompilerCrep.source`. -/
theorem staticFrontBudget_sourceDeclarations_eq :
    staticFrontBudget sourceDeclarations (ofString "main") =
      listBudget ConcreteCompilerCrep.source := by
  unfold staticFrontBudget
  rw [compileProgDeclsHOLW_sourceDeclarations_eq]

/-- Under `listBudget ConcreteCompilerCrep.source ≤ 448`, `frontBudget sourceDeclarations (ofString "main") ≤ 448`. -/
theorem frontBudget_sourceDeclarations_le_448
    (h_list : listBudget ConcreteCompilerCrep.source ≤ 448) :
    frontBudget sourceDeclarations (ofString "main") ≤ 448 := by
  have h1 := frontBudget_le_staticFrontBudget sourceDeclarations (ofString "main")
  rw [staticFrontBudget_sourceDeclarations_eq] at h1
  exact Nat.le_trans h1 h_list

/-- Concrete upper bound on `wordClock` and `certifiedStackClock` for `sourceDeclarations` / `"main"`. -/
theorem wordClock_and_certifiedStackClock_bound
    (h_static_bound : staticFrontBudget sourceDeclarations (ofString "main") ≤ 448)
    (k_pan : Nat) :
    wordClock sourceDeclarations (ofString "main") k_pan ≤ 449 * k_pan + 452 ∧
      certifiedStackClock sourceDeclarations (ofString "main") k_pan ≤ 2 * (449 * k_pan + 452) := by
  have h1 : staticFrontBudget sourceDeclarations (ofString "main") + 1 ≤ 449 := by omega
  have h2 : (staticFrontBudget sourceDeclarations (ofString "main") + 1) * k_pan ≤ 449 * k_pan :=
    Nat.mul_le_mul_right k_pan h1
  have hw : wordClock sourceDeclarations (ofString "main") k_pan ≤ 449 * k_pan + 452 := by
    unfold wordClock
    omega
  refine ⟨hw, ?_⟩
  unfold certifiedStackClock
  omega

/-- Equality between `ConcreteFrontendState.word` and `frontendWordState` over `ConcreteStackLayout.stack`. -/
theorem concreteFrontendState_word_eq_frontendWordState
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config) :
    ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf =
      frontendWordState baselineMachineConfig.target.config sourceDeclarations
        wprog InitECandidate.bitmaps
        (ConcreteStackLayout.stack oracles input t m bitmapsDm sdm p ltconf) ltconf := rfl

/-- Byte-alignment of `(sourceInitialState input).topAddr`. -/
theorem sourceInitialState_topAddr_byteAligned (input : Guest.InputBlob) :
    panGlobalsByteAlignedHOL (sourceInitialState input).topAddr := by
  change panByteAlignHOL (BitVec.ofNat 64 heapEnd) = BitVec.ofNat 64 heapEnd
  decide

/-- Concrete instantiation of `FrontendRelation` for `sourceInitialState input` and
`ConcreteFrontendState.word` under `goodInitState` and non-failing semantics. -/
theorem concrete_frontendRelation
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm)
    (hnonfail : PanSemStateFiniteExact.semanticsDecls
      (sourceInitialState input) (ofString "main") sourceDeclarations ≠ .fail) :
    FrontendRelation (sourceInitialState input)
      (ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf)
      baselineMachineConfig.target.config.isa sourceDeclarations (ofString "main")
      globalsWords ConcreteFrontendState.heapLength := by
  obtain ⟨hmem_w, hnolab, hmd, hsh, hbe, hffi, hcurr, hlen⟩ :=
    ConcreteFrontendState.fields oracles input t m bitmapsDm sdm wprog p ltconf initialized
  have htop : (sourceInitialState input).topAddr =
      (sourceInitialState input).baseAddr + 2 * ConcreteFrontendState.heapLength -
        panBytesInWord 64 * BitVec.ofNat 64 globalsWords := by
    change BitVec.ofNat 64 heapEnd =
      BitVec.ofNat 64 sourceBase + 2 * ConcreteFrontendState.heapLength -
        panBytesInWord 64 * BitVec.ofNat 64 globalsWords
    decide
  have hloc : sptLookup 0
      (ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf).locals =
      some (WordLocW.loc 1 0) :=
    sptLookup_sptInsert_zero (WordLocW.loc 1 0) Spt.ln
  refine ⟨hmem_w, hnolab, rfl, sourceGlobalsSize.symm, sourceDistinctParams,
    hmd, hsh, hbe, hffi, hcurr, hlen, htop, sourceDistinctFunctions,
    sourceInitialState_topAddr_byteAligned input,
    SourceHeapFacts.source_globals_allocatable input,
    rfl, rfl, rfl, rfl, sourceExceptionBound, rfl, hloc, Or.inr rfl, hnonfail⟩

/-- Stage 1->2 (`PanSem -> WordSem`) concrete entry-class agreement at `wordClock`. -/
theorem concrete_pan_to_word_static_class
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm)
    (hnonfail : PanSemStateFiniteExact.semanticsDecls
      (sourceInitialState input) (ofString "main") sourceDeclarations ≠ .fail)
    (h_static_bound : staticFrontBudget sourceDeclarations (ofString "main") ≤ 448)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan : Nat) (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (hnt_src : res_src ≠ some .timeOut) :
    wordEntryClass (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec 64))
      { ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf with
        clock := 449 * k_pan + 452 }).1 = panEntryClass res_src := by
  have hfront := concrete_frontendRelation oracles input t m bitmapsDm sdm wprog p ltconf
    initialized hnonfail
  have hclass := pan_to_word_static_class (sourceInitialState input)
    (ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf)
    baselineMachineConfig.target.config.isa sourceDeclarations (ofString "main")
    globalsWords ConcreteFrontendState.heapLength
    hfront stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src hnt_src
  have hbud := Nat.le_trans (frontBudget_le_staticFrontBudget sourceDeclarations (ofString "main")) h_static_bound
  have henough : (frontBudget sourceDeclarations (ofString "main") + 1) * k_pan +
      (frontBudget sourceDeclarations (ofString "main") + 4) ≤ 449 * k_pan + 452 := by
    have h1 : frontBudget sourceDeclarations (ofString "main") + 1 ≤ 449 := by omega
    have h2 : (frontBudget sourceDeclarations (ofString "main") + 1) * k_pan ≤ 449 * k_pan :=
      Nat.mul_le_mul_right k_pan h1
    omega
  have hnt_old : (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec 64))
      { ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf with
        clock := (frontBudget sourceDeclarations (ofString "main") + 1) * k_pan +
          (frontBudget sourceDeclarations (ofString "main") + 4) }).1 ≠ some .timeOut :=
    pan_to_word_affine_notTimeOut (sourceInitialState input)
      (ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf)
      baselineMachineConfig.target.config.isa sourceDeclarations (ofString "main")
      globalsWords ConcreteFrontendState.heapLength
      hfront stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src hnt_src
  let oldClock := (frontBudget sourceDeclarations (ofString "main") + 1) * k_pan +
    (frontBudget sourceDeclarations (ofString "main") + 4)
  rcases hrun : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec 64))
      { ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf with
        clock := oldClock } with ⟨r, post⟩
  have hlift := WordSemStateFiniteExact.evaluate_add_clock (449 * k_pan + 452 - oldClock)
    (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec 64))
    { ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf with clock := oldClock }
    r post ⟨hrun, by rw [hrun] at hnt_old; exact hnt_old⟩
  have hclockEq : oldClock + (449 * k_pan + 452 - oldClock) = 449 * k_pan + 452 :=
    Nat.add_sub_of_le henough
  simp only [hclockEq] at hlift
  change wordEntryClass (WordSemStateFiniteExact.evaluate
    (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec 64))
    { ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf with
      clock := 449 * k_pan + 452 }).1 = panEntryClass res_src
  rw [hlift]
  change wordEntryClass (WordSemStateFiniteExact.evaluate
    (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec 64))
    { ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf with
      clock := oldClock }).1 = panEntryClass res_src at hclass
  rw [hrun] at hclass
  exact hclass

/-- Stage 1->2 (`PanSem -> WordSem`) affine non-`.timeOut` transfer theorem
at concrete affine clock `(448 + 1) * k_pan + (448 + 4) = 449 * k_pan + 452`. -/
theorem stage1_to_2_pan_to_word_affine_not_timeOut {width : Nat} [NeZero width] {C σ : Type}
    (source : PanSemStateFiniteExact width σ) (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture) (code : List (DeclHOL width)) (start : MlS)
    (globalsSize : Nat) (heapLen : BitVec width)
    (h : FrontendRelation source target arch code start globalsSize heapLen)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact width σ)
    (hst : decsStcnamesHOLExact [] code = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { source with structs := stCtxt } (fun a => Classical.propDecidable (source.memaddrs a))
      code = some s_decls)
    (k_pan k_word : Nat)
    (h_word_clock : (frontBudget code start + 1) * k_pan + (frontBudget code start + 4) ≤ k_word)
    (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (hnt_src : res_src ≠ some .timeOut) :
    (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := k_word }).1 ≠ some .timeOut := by
  let oldClock := (frontBudget code start + 1) * k_pan + (frontBudget code start + 4)
  have hnt_old := pan_to_word_affine_notTimeOut source target arch code start globalsSize heapLen
    h stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src hnt_src
  rcases hrun : WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := oldClock } with ⟨r, post⟩
  have hnt_r : r ≠ some .timeOut := by
    change (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := oldClock }).1 ≠ some .timeOut at hnt_old
    rw [hrun] at hnt_old
    exact hnt_old
  have hlift := WordSemStateFiniteExact.evaluate_add_clock (k_word - oldClock)
    (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
    { target with clock := oldClock } r post ⟨hrun, hnt_r⟩
  have hclockEq : oldClock + (k_word - oldClock) = k_word := Nat.add_sub_of_le h_word_clock
  simp only [hclockEq] at hlift
  change (WordSemStateFiniteExact.evaluate
    (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
    { target with clock := k_word }).1 ≠ some .timeOut
  rw [hlift]
  exact hnt_r

/-- Concrete Stage 1->2 (`PanSem -> WordSem`) non-`.timeOut` transfer on `sourceDeclarations`
and `ConcreteFrontendState.word` (`pipelinePanToWordInitState`) for any clock `k_word ≥ 449 * k_pan + 452`. -/
theorem concrete_stage1_to_2_pan_to_word_not_timeOut
    (oracles : List (Option (Spt Nat))) (input : Guest.InputBlob)
    (t : AsmState 64) (m : BitVec 64 → WordLocW 64)
    (bitmapsDm sdm : BitVec 64 → Bool)
    (wprog : List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (p : List (Nat × StackLang.HolProg 64)) (ltconf : LabToTarget.Config)
    (initialized : goodInitState baselineMachineConfig baselineInstalledState
      InitECandidate.nativeCode 3788 t m (ConcreteInitMemory.dataDomain oracles t bitmapsDm) sdm)
    (hnonfail : PanSemStateFiniteExact.semanticsDecls
      (sourceInitialState input) (ofString "main") sourceDeclarations ≠ .fail)
    (h_static_bound : staticFrontBudget sourceDeclarations (ofString "main") ≤ 448)
    (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hst : decsStcnamesHOLExact [] sourceDeclarations = some stCtxt)
    (hev_decls : @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
      { sourceInitialState input with structs := stCtxt }
      (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
      sourceDeclarations = some s_decls)
    (k_pan k_word : Nat)
    (h_word_clock : 449 * k_pan + 452 ≤ k_word)
    (res_src : Option (PanSemResultExact 64))
    (s_src_post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState
      { s_decls with clock := k_pan }
      (.call none (ofString "main") [] : ProgHOL 64) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (hnt_src : res_src ≠ some .timeOut) :
    (WordSemStateFiniteExact.evaluate
      (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec 64))
      { ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf with
        clock := k_word }).1 ≠ some .timeOut := by
  have hfront := concrete_frontendRelation oracles input t m bitmapsDm sdm wprog p ltconf
    initialized hnonfail
  have hbud := Nat.le_trans (frontBudget_le_staticFrontBudget sourceDeclarations (ofString "main")) h_static_bound
  have hle : (frontBudget sourceDeclarations (ofString "main") + 1) * k_pan +
      (frontBudget sourceDeclarations (ofString "main") + 4) ≤ k_word := by
    have h1 : frontBudget sourceDeclarations (ofString "main") + 1 ≤ 449 := by omega
    have h2 : (frontBudget sourceDeclarations (ofString "main") + 1) * k_pan ≤ 449 * k_pan :=
      Nat.mul_le_mul_right k_pan h1
    omega
  exact stage1_to_2_pan_to_word_affine_not_timeOut (sourceInitialState input)
    (ConcreteFrontendState.word oracles input t m bitmapsDm sdm wprog p ltconf)
    baselineMachineConfig.target.config.isa sourceDeclarations (ofString "main")
    globalsWords ConcreteFrontendState.heapLength
    hfront stCtxt s_decls hst hev_decls k_pan k_word hle res_src s_src_post hev_call hne_src hnt_src

end InitECandidate.Solver.Wave8Stage.R12_Stage1To2BoundArgon
