import InitECandidate.Solver.SelfContainedConcretePipelineMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.ConcreteStage1To5Transfer

open Classical
open InitE
open InitECandidate.Proofs
open InitECandidate.Solver.SelfContainedBoundedCertificate
open InitECandidate.Solver.SelfContainedPipelineBridge
open InitECandidate.Solver.SelfContainedConcretePipelineMaster
open Flapjack
open Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.Proofs.PanToTarget
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof
open Flapjack.Compiler.Backend.RiscVConfig
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabSem

def CoveredSourceTicksConsumedBounded (K_pan_max : Nat) : Prop :=
  ∀ (input : Guest.InputBlob),
    Guest.GasLimit.declaredGasLimit input ≤ 200000000 →
    ∀ (outcome : HolOutcome) (events : List HolIoEvent),
      sourceBehaviour input = .terminate outcome events →
      coveredOutcome outcome →
      ∀ (stCtxt : StructContextExact) (s_decls : PanSemStateFiniteExact 64 Guest.HostMemory),
        decsStcnamesHOLExact [] sourceDeclarations = some stCtxt →
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite 64 Guest.HostMemory _
          { sourceInitialState input with structs := stCtxt }
          (fun a => Classical.propDecidable ((sourceInitialState input).memaddrs a))
          sourceDeclarations = some s_decls →
        (PanSemStateFiniteExact.evaluateHOLFiniteState
          { s_decls with clock := K_pan_max }
          (.call none (ofString "main") [] : ProgHOL 64)).1 ≠ some .timeOut

def concreteTargetK (K_pan_max : Nat) : Nat :=
  bootstrapSteps + linearPipelineTargetBudget K_pan_max 1 0 8 0 4

theorem concreteTargetK_le_maxYukonK (K_pan_max : Nat)
    (hK : K_pan_max ≤ 10 ^ 30) :
    concreteTargetK K_pan_max ≤ (10 ^ 299 - 1) / 10 ^ 4 := by
  unfold concreteTargetK linearPipelineTargetBudget
  rw [InitE.bootstrapSteps_eq]
  omega

open InitECandidate.Solver.FastEnv

theorem stage2_word_not_timeOut {width : Nat} [NeZero width] {C σ : Type}
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
    (k_pan : Nat) (k_word : Nat → Nat)
    (h_word_clock : ∀ k', k_word k' = (k_pan + 1) + k')
    (res_src : Option (PanSemResultExact width))
    (s_src_post : PanSemStateFiniteExact width σ)
    (hev_call : PanSemStateFiniteExact.evaluateHOLFiniteState { s_decls with clock := k_pan }
      (.call none start [] : ProgHOL width) = (res_src, s_src_post))
    (hne_src : panEntryClass res_src ≠ .RunError)
    (hnt_src : res_src ≠ some .timeOut) :
    ∃ k', (WordSemStateFiniteExact.evaluate
      (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
      { target with clock := k_word k' }).1 ≠ some .timeOut := by
  obtain ⟨k', t_word, res_word, hrun, -, hclass⟩ :=
    SelfContainedStageBounds.pan_to_word_clocked_sim source target arch code start globalsSize heapLen
      h stCtxt s_decls hst hev_decls k_pan res_src s_src_post hev_call hne_src
  refine ⟨k', ?_⟩
  rw [h_word_clock, hrun]
  intro htimeout
  change res_word = some WordSemResult.timeOut at htimeout
  subst res_word
  rw [← hclass] at hne_src
  clear h hrun hev_call hev_decls hst
  cases res_src with
  | none =>
    simp_all [LoopToWordStateRelImpSemanticsSupport.wordEntryClass, panEntryClass]
  | some r =>
    cases r <;>
      simp_all [LoopToWordStateRelImpSemanticsSupport.wordEntryClass, panEntryClass]

theorem stage3_stack_not_timeOut {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k_reg : Nat)
    (s : WordSemStateFiniteExact width (Nat × C) F)
    (t : StackSemStateFiniteExact width C F)
    (start k_word : Nat) (k_stack : Nat → Nat)
    (h_stack_clock : ∀ ck, k_stack ck = k_word + ck)
    (res : Option (WordSemResult width))
    (s1 : WordSemStateFiniteExact width (Nat × C) F)
    (related : WordToStackProofs.stateRel ac k_reg 0 0 s t [] 0)
    (safe : WordSemStateFiniteExact.wordLangSafeForSpace s start)
    (hrun : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      { s with clock := k_word } = (res, s1))
    (hne : res ≠ some .error)
    (hnt : res ≠ some .timeOut) :
    ∃ ck, (StackSemEvaluate.evaluate ((.call none (.inl start) none : StackLang.HolProg width),
      { t with clock := k_stack ck })).1 ≠ some .timeOut := by
  obtain ⟨ck, t1, hrun', -⟩ :=
    SelfContainedStageBounds.word_to_stack_clocked_sim ac k_reg s t start k_word res s1
      related safe hrun hne
  refine ⟨ck, ?_⟩
  rw [h_stack_clock, hrun']
  intro htimeout
  change res.map WordToStackProofs.CompCorrect.compileResult = some StackSemResult.timeOut
    at htimeout
  clear hrun hrun' related safe
  cases res with
  | none => simp at htimeout
  | some r =>
    cases r <;> simp_all [WordToStackProofs.CompCorrect.compileResult]

end InitECandidate.Solver.ConcreteStage1To5Transfer
