import InitECandidate.Solver.SelfContainedStageBounds
import InitECandidate.Solver.Wave8Stage.CrepCostEntry

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 200000

namespace InitECandidate.Solver.Wave8Stage.FrontendCostTransfer
open Classical InitE Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString Flapjack.Compiler.Encoders.Asm
open Flapjack.LoopToWord.CompileCorrect
open InitECandidate.Solver.SelfContainedStageBounds

def simplifiedCode {width : Nat} [NeZero width]
    (code : HolFiniteMapExact MlString (List Nat × CrepProgHOL width)) :=
  code.map2 (fun entry => (entry.2.1, crepSimpProgHOL entry.2.2))

noncomputable def crepBudget {width : Nat} [NeZero width]
    (code : List (MlString × List Nat × CrepProgHOL width)) : Nat :=
  CrepCodeBudget.codeBound (simplifiedCode (alistToFmapCodeExact code))

noncomputable def frontBudget {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) (start : MlString) : Nat :=
  crepBudget (compileProgDeclsHOLW (compileTopExactHOL
    (Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)) start))

theorem crep_to_loop_clocked_sim {width : Nat} [NeZero width] {σ : Type}
    (s : CrepSemHOLState width σ) (t : LoopSemStateFiniteExact width σ)
    (crep_code : List (MlString × List Nat × CrepProgHOL width))
    (start : MlString) (lc : Nat) (c : AsmArchitecture)
    (prog : CrepProgHOL width) (k : Nat)
    (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
    (hmd : s.memaddrs = (fun address => t.mdomain address = true))
    (hbe : s.be = t.be)
    (hsh : s.shMemaddrs = (fun address => t.shMdomain address = true))
    (hffi : s.ffi = t.ffi)
    (hbase : s.baseAddr = t.baseAddr)
    (htop : s.topAddr = t.topAddr)
    (hmem : crepToLoopMemRelHOLExact s.memory t.memory s.memaddrs)
    (hglob : crepToLoopGlobalsRelHOLExact s.globals t.globals)
    (hdist : (crep_code.map Prod.fst).Nodup)
    (hscode : s.code = alistToFmapCodeExact crep_code)
    (htcode : t.code = sptFromAList (compileProgHOLExact c crep_code))
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hmf : (crepToLoopMakeFuncsExactHOL crep_code).lookup start = some (lc, 0))
    (hprog : holAlookup crep_code start = some ([], prog))
    (hev : evalCrepSemHOLProgExact { s with clock := k } (.call none start []) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ k' t',
      LoopSemStateFiniteExact.evaluate
        (.call none (some lc) [] none : HolLoopProg width)
        { t with clock := k + k' } =
        (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res, t') ∧
      s1.ffi = t'.ffi ∧ k' ≤ crepBudget crep_code * k + 3 := by
  let nctxt : CrepToLoopContextExact :=
    mkCtxtExact c HolFiniteMapExact.empty (crepToLoopMakeFuncsExactHOL crep_code) 0
  have hcode2 : crepToLoopCodeRel2Exact nctxt s.code t.code := by
    rw [hscode, htcode]
    exact mkCtxtCodeImpCodeRel2Exact c crep_code start prog ⟨hdist, hprog⟩
  have hlc : findLabExact nctxt start = lc := by
    simp [findLabExact, nctxt, mkCtxtExact, hmf]
  have hdv : crepToLoopDistinctVarsExact nctxt.vars := by
    intro x y n m hx
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hx
  have hcm : crepToLoopCtxtMaxExact nctxt.vmax nctxt.vars := by
    intro v m hv
    simp [nctxt, mkCtxtExact, HolFiniteMapExact.empty] at hv
  have hmf' : (crepToLoopMakeFuncsExactHOL crep_code).lookup start =
      some (findLabExact nctxt start, 0) := by
    rw [hlc]; exact hmf
  obtain ⟨k', res', t', hrun, hsr, hres, hcost⟩ :=
    CrepCostEntry.compCall nctxt s.code t.code start
      { s with clock := k } res s1 { t with clock := k } crep_code lc prog hcode2 hev
      ⟨hbe, hsh, hmd, rfl, hffi, hbase, htop, hmem, hglob, hloc, rfl, rfl⟩ hmf'
      ⟨hlc, hscode, rfl, hprog, hdv, hcm⟩ hne
  rw [hlc] at hrun
  have hrun' : LoopSemStateFiniteExact.evaluate (.call none (some lc) [] none : HolLoopProg width)
      { t with clock := k + k' } = (res', t') := by
    have heq : ({ { t with clock := k } with clock := k + k' } :
        LoopSemStateFiniteExact width σ) = { t with clock := k + k' } := by
      cases t; rfl
    rw [← heq]
    exact hrun
  rw [hres] at hrun'
  refine ⟨k', t', hrun', hsr.2.2.2.2.1, ?_⟩
  simpa only [crepBudget, simplifiedCode, crepSimpMapcsHOL, hscode] using hcost

open PanToCrepStateRelImpSemanticsTop
open LoopToWordStateRelImpSemanticsSupport in
private theorem list_lookup_isSome_iff_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : (List.lookup k l).isSome = true ↔ k ∈ l.map Prod.fst := by
  induction l with
  | nil => simp only [List.lookup, Option.isSome, List.map_nil, List.not_mem_nil, reduceCtorEq]
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    by_cases h : k = a
    · subst h; simp only [List.lookup_cons, beq_self_eq_true, Option.isSome_some, List.map_cons, List.mem_cons, true_or]
    · have hbeq : (k == a) = false := beq_false_of_ne h
      simp only [List.lookup_cons, hbeq, ih, List.map_cons, List.mem_cons, h, false_or]

private theorem fupdateList_empty_eq_lookup_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) :
    FUPDATE_LIST FEMPTY l k = List.lookup k l.reverse := by
  have := FLOOKUP_FUPDATE_LIST_reverse_eq_lookup l.reverse k
  simpa [FLOOKUP] using this

private theorem alistToFmap_eq_lookup_local {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) : FLOOKUP (alistToFmap l) k = List.lookup k l := by
  induction l with
  | nil => rfl
  | cons e l ih =>
    obtain ⟨a, b⟩ := e
    change FLOOKUP (FUPDATE (alistToFmap l) (a, b)) k = _
    rw [FLOOKUP_update, ih, List.lookup_cons]
    by_cases hk : k = a
    · subst hk; simp
    · have h1 : (a == k) = false := by simp [Ne.symm hk]
      have h2 : (k == a) = false := by simp [hk]
      simp [h1, h2]

open PanToCrepStateRelImpSemanticsTop
open LoopToWordStateRelImpSemanticsSupport in

theorem pan_to_crep_to_word_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
    (globalState T : PanSemStateFiniteExact width σ)
    (target : WordSemStateFiniteExact width C σ)
    (arch : AsmArchitecture)
    (panCode : List (DeclHOL width)) (start : MlS)
    (heapLen : BitVec width)
    (hnolabels : noLabelsHOL target.memory (fun address => target.mdomain address = true))
    (_hstart : start = ofString "main")
    (hmdomain : (fun address => target.mdomain address = true) = globalState.memaddrs)
    (hshdomain : (fun address => target.shMdomain address = true) = globalState.shMemaddrs)
    (hbe : target.be = globalState.be)
    (hffi : target.ffi = globalState.ffi)
    (hcurrheap : target.store.lookup .currHeap = some (.word globalState.baseAddr))
    (hheaplen : target.store.lookup .heapLength = some (.word heapLen))
    (htop' : globalState.topAddr = globalState.baseAddr + (2 : BitVec width) * heapLen)
    (hmem_glob : globalState.memory = wlocWlabHOL ∘ target.memory)
    (hcode : globalState.code = HolFiniteMapExact.empty)
    (hglobals : globalState.globals = HolFiniteMapExact.empty)
    (hlocals : globalState.locals = HolFiniteMapExact.empty)
    (heshapes : globalState.eshapes = HolFiniteMapExact.empty)
    (htcode : target.code = sptFromAList
      (loopToWordCompileProgHOL (compileProgHOLExact arch (compileProgDeclsHOLW panCode))))
    (hloc0 : sptLookup 0 target.locals = some (WordLocW.loc 1 0))
    (hdim : goodDimindex width)
    (hdist_pan : ((functionsHOL panCode).map Prod.fst).Nodup)
    (hlocal_pan : ∀ entry ∈ functionsHOL panCode, localisedProgHOL entry.2.2.1 = true)
    (hall_pan : panCode.all (fun x => isFunctionHOL x || isExnDeclHOL x) = true)
    (hpanSize : sizeOfEidsHOL panCode < 2 ^ width)
    (hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)).lookup start =
      some (firstLoopName, 0))
    (hglobalnf : PanSemStateFiniteExact.semanticsDecls globalState start panCode ≠ .fail)
    (hevT : @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _
      { globalState with structs := [] }
      (fun a => Classical.propDecidable (globalState.memaddrs a)) panCode = some T)
    (c : Nat) (res_pan : Option (PanSemResultExact width))
    (s_pan_post : PanSemStateFiniteExact width σ)
    (hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := c }
      (.call none start [] : ProgHOL width) = (res_pan, s_pan_post))
    (hne_pan : panEntryClass res_pan ≠ .RunError) :
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
        { target with clock := c + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_pan_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_pan ∧
      k' ≤ crepBudget (compileProgDeclsHOLW panCode) * c + 3 := by
  classical
  have hne_pan_err : res_pan ≠ some .error := by
    intro h; subst h; exact hne_pan rfl

  let s0 : PanSemStateFiniteExact width σ := { globalState with structs := [] }
  let p0 := PanPropsEvalStateFiniteExact.ofPanSemFinite s0
  let hdec : DecidablePred p0.memaddrs := fun a => Classical.propDecidable _
  have hcanon : PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical p0 panCode =
      some (PanPropsEvalStateFiniteExact.ofPanSemFinite T) := by
    unfold PanPropsEvalStateFiniteExact.evaluateDeclsPanPropsCanonical
    have key : ∀ (st : PanSemStateFiniteExact width σ) (h1 h2 : DecidablePred st.memaddrs),
        @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ st h1 panCode =
          @PanSemStateFiniteExact.evaluateDeclsHOLFinite width σ _ st h2 panCode := by
      intro st h1 h2
      rw [Subsingleton.elim h1 h2]
    have hE := (key p0.toPanSemFinite inferInstance hdec).trans hevT
    rw [hE]
    rfl
  have hshape := PanPropsEvalStateFiniteExact.evaluateDeclsOnlyFunsAndExnDeclsHOLFinite p0 panCode
    (PanPropsEvalStateFiniteExact.ofPanSemFinite T) hall_pan hcanon
  have hT_eq : T = { s0 with
      code := HolFiniteMapExact.empty.updateList (functionsHOL panCode)
      eshapes := HolFiniteMapExact.empty.updateList (exceptionsHOL panCode) } := by
    have h := congrArg PanPropsEvalStateFiniteExact.toPanSemFinite hshape
    simp only [PanPropsEvalStateFiniteExact.toPanSemFinite_ofPanSemFinite] at h
    rw [h]
    simp [PanPropsEvalStateFiniteExact.toPanSemFinite, p0,
      PanPropsEvalStateFiniteExact.ofPanSemFinite, s0, hcode, heshapes]

  let crepState := crepStateHOL globalState panCode globalState.memory
  let crepStatePre := { crepState with
    code := HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW panCode).reverse }
  have hsr_crep : panToCrepStateRelFiniteExact T crepStatePre := by
    rw [hT_eq]
    simp [panToCrepStateRelFiniteExact, s0, crepStatePre, crepState, crepStateHOL,
      hglobals, HolFiniteMapExact.empty]
  have hscode_T : T.code = HolFiniteMapExact.empty.updateList (functionsHOL panCode).reverse := by
    rw [hT_eq]
    apply HolFiniteMapExact.ext
    funext k
    simp only [HolFiniteMapExact.lookup_updateList]
    change FUPDATE_LIST FEMPTY _ k = FUPDATE_LIST FEMPTY _ k
    rw [fupdateList_empty_eq_lookup_local, fupdateList_empty_eq_lookup_local, List.reverse_reverse,
      PanGlobalsCompileTopSemanticsDecls.lookupReverseOfNodup _ _ hdist_pan]
  have hdom_T : ∀ key, (T.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome := by
    intro key
    rw [hT_eq]
    show ((HolFiniteMapExact.empty.updateList (exceptionsHOL panCode)).lookup key).isSome =
      ((getEidsFromDeclsHOL panCode).lookup key).isSome
    rw [HolFiniteMapExact.lookup_updateList, holFmapAsFiniteSupportResultWitness_getEidsFromDeclsHOL,
      alistToFmap_eq_lookup_local]
    change (FUPDATE_LIST FEMPTY _ key).isSome = _
    rw [fupdateList_empty_eq_lookup_local]
    apply Bool.eq_iff_iff.mpr
    rw [list_lookup_isSome_iff_local, list_lookup_isSome_iff_local, List.map_reverse,
      List.mem_reverse, getEidsEntriesHOL_eq_lengthBased]
    simp only
    rw [List.map_fst_zip (by simp)]
  have hloc_T : T.locals = HolFiniteMapExact.empty := by
    rw [hT_eq]; exact hlocals
  obtain ⟨res_crep1, t_crep1, hrun_crep1, hne_crep1_val, hffi_crep1, hclass_crep1⟩ :=
    pan_to_crep_clocked_agree T crepStatePre panCode start c res_pan s_pan_post
      hsr_crep hdist_pan hscode_T rfl hloc_T hlocal_pan hpanSize hdom_T hev_pan hne_pan_err

  have hne_crep1 : (evalCrepSemHOLProgExact { crepStatePre with clock := c }
      (.call none start [])).1 ≠ some .error := by
    rw [hrun_crep1]
    exact hne_crep1_val
  have hinl := crep_inline_clocked_agree crepStatePre crepState
    (compileToCrepExactHOLW panCode) start
    ((functionsHOL (panCode.filter inlinableHOL)).map Prod.fst) c
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
    (firstCompileToCrepAllDistinctExact panCode hdist_pan) rfl
    (by simp [crepState, crepStateHOL, compileProgDeclsHOLW, alistToFmapCodeExact])
    hne_crep1
  rcases hrun_crep : evalCrepSemHOLProgExact { crepState with clock := c }
      (.call none start []) with ⟨res_crep, t_crep⟩
  have hres_crep : res_crep = res_crep1 := by
    have h1 := hinl.1
    rw [hrun_crep, hrun_crep1] at h1
    exact h1
  have hffi_crep : t_crep.ffi = t_crep1.ffi := by
    have h2 := hinl.2
    rw [hrun_crep, hrun_crep1] at h2
    exact h2

  let crepCode := compileProgDeclsHOLW panCode
  let loopState := loopStateHOL crepState arch crepCode target.clock target.memory
  have hcrep_sem := stateRelImpSemanticsDeclsPanToCrep globalState crepState panCode start
    ⟨(by simp [panToCrepStateRelFiniteExact, crepState, crepStateHOL,
          hglobals, HolFiniteMapExact.empty]),
      hdist_pan, hcode, rfl, hlocals, heshapes, hlocal_pan, hall_pan, hpanSize, hglobalnf⟩
  have hcrepnf : crepSemantics crepState start ≠ .fail := by
    rw [hcrep_sem]; exact hglobalnf
  have hdist_crep : (crepCode.map Prod.fst).Nodup :=
    panToCrepFirstCompileProgAllDistinctExact panCode hdist_pan
  obtain ⟨prog_crep, hprog_crep⟩ :=
    crepSemantics_ne_fail_imp_holAlookup crepState crepCode start rfl rfl hdist_crep hcrepnf
  have hne_crep : res_crep ≠ some .error := by
    rw [hres_crep]
    intro h
    subst h
    rw [hrun_crep1] at hne_crep1
    exact hne_crep1 rfl
  obtain ⟨k', t_loop, hrun_loop, hffi_loop, hcost_loop⟩ :=
    crep_to_loop_clocked_sim crepState loopState crepCode start firstLoopName arch
      prog_crep c res_crep t_crep
      (by simp [loopState, loopStateHOL]) rfl
      (by simp [loopState, loopStateHOL]) rfl rfl rfl
      (by intro address ha
          have ha' : target.mdomain address = true := (congrFun hmdomain address).symm ▸ ha
          obtain ⟨w, hw⟩ := hnolabels address ha'
          simp [crepState, crepStateHOL, loopState, loopStateHOL, hmem_glob,
            wlocWlabHOL, wlabWlocExact, hw])
      (by intro address value he
          simp [crepState, crepStateHOL, HolFiniteMapExact.empty] at he)
      hdist_crep rfl rfl rfl hmf hprog_crep hrun_crep hne_crep

  have hdm : loopState.mdomain = target.mdomain := by
    funext address
    have hd := congrFun hmdomain address
    apply Bool.eq_iff_iff.mpr
    simpa [loopState, loopStateHOL, crepState, crepStateHOL] using Iff.of_eq hd.symm
  have hsh : loopState.shMdomain = target.shMdomain := by
    funext address
    have hd := congrFun hshdomain address
    simp [loopState, loopStateHOL, crepState, crepStateHOL, ← hd]
  have hparamsLoop := crepToLoopCompileProgDistinctParamsHOLExact crepCode arch
    (compileProgDeclsHOLW_params_nodup panCode)
  have hrel_word : loopToWordStateRelHOLExact loopState target := by
    refine ⟨heapLen, rfl, hdm.symm, hsh.symm, rfl, hbe, hffi, hcurrheap, hheaplen, htop', ?_, ?_⟩
    · intro name value hl
      simp [loopState, loopStateHOL, HolFiniteMapExact.empty] at hl
    · intro name params body hl
      constructor
      · rw [htcode]
        exact loopToWordLookupProgSomeLookupCompileProg _ name params body hl
      · apply of_decide_eq_true
        apply (List.all_eq_true.mp hparamsLoop) (name, params, body)
        apply sptAListLookup_mem name (compileProgHOLExact arch crepCode) (params, body)
        simpa only [loopState, loopStateHOL, sptLookup_sptFromAList] using hl
  have hne_loop : Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res_crep ≠ some .error := by
    rcases res_crep with _ | r_val
    · intro h; cases h
    · cases r_val <;> intro h <;> first | exact hne_crep rfl | cases h
  obtain ⟨t_word, res_word, hrun_word, hffi_word, hrc_word⟩ :=
    loop_to_word_clocked_agree loopState target firstLoopName (c + k')
      (Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop res_crep) t_loop
      hrel_word rfl hdim hloc0 hrun_loop hne_loop
  refine ⟨k', t_word, res_word, hrun_word, ?_, ?_, hcost_loop⟩
  · rw [hffi_word, ← hffi_loop, hffi_crep, hffi_crep1]
  · rw [← hclass_crep1, ← hres_crep] at hne_pan ⊢
    rcases res_crep with _ | (_ | _ | _ | _ | _ | _) <;>
      dsimp only [Pancake.CrepToLoop.Proofs.NCompileCorrect.resultToLoop, resultCase] at hne_pan hrc_word ⊢ <;>
      first | exact False.elim hrc_word | exact False.elim (hne_pan rfl) |
        (rcases hrc_word with ⟨rfl, _⟩; rfl) |
        (rcases hrc_word with ⟨_, rfl, _⟩; rfl) |
        (rcases hrc_word with ⟨_, _, rfl, _⟩; rfl) |
        (subst hrc_word; rfl)

open LoopToWordStateRelImpSemanticsSupport in

theorem pan_to_word_clocked_sim {width : Nat} [NeZero width] {C σ : Type}
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
    (hne_src : panEntryClass res_src ≠ .RunError) :
    ∃ k' t_word res_word,
      WordSemStateFiniteExact.evaluate
        (.call none (some firstLoopName) [0] none : WordLangProgHOL (BitVec width))
        { target with clock := (k + 1) + k' } = (res_word, t_word) ∧
      t_word.ffi.ioEvents = s_src_post.ffi.ioEvents ∧
      wordEntryClass res_word = panEntryClass res_src ∧
      k' ≤ frontBudget code start * (k + 1) + 3 := by
  classical
  have hne_src_err : res_src ≠ some .error := by
    intro herr; subst herr; exact hne_src rfl
  obtain ⟨hmem, hnolabels, hstart, hsize, _hparams, hmdomain, hshdomain, hbe, hffi,
    hcurrheap, hheaplen, htop, hdist, halign, halloc, hcode, htcode, hglobals,
    hlocals, heids, heshapes, hloc0, hdim, hfail⟩ := h
  have hglobalsSem := Pancake.Proofs.PanToWord.InitialComposition.initialToGlobalsSemantics
    source target code start globalsSize hfail hdist hcode hlocals hglobals heshapes
    hsize halloc halign hdim hmem
  let structCode := Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)
  let panCode := compileTopExactHOL structCode start
  let globalState : PanSemStateFiniteExact width σ :=
    { source with
      topAddr := source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize
      memaddrs := fun address => source.memaddrs address ∨
        Compiler.Backend.StackRemove.addresses source.topAddr globalsSize address
      memory := wlocWlabHOL ∘ target.memory
      locals := source.locals }
  have hglobalnf : PanSemStateFiniteExact.semanticsDecls globalState start panCode ≠ .fail := by
    rw [← hglobalsSem]; exact hfail
  have hstructnf : PanSemStateFiniteExact.semanticsDecls source start structCode ≠ .fail := by
    have h1 := Pancake.Proofs.PanStructs.CompileTopSemanticsDeclsExact.compileTopSemanticsDeclsExact
      source start (panSimpDeclsHOL code)
    have hs := PanSimp.stateRelImpSemanticsDeclsHOL source source code start
      ⟨(by refine ⟨?_, (fun _ h => h), ?_⟩
           · cases source; rfl
           · intro f vs p sh he; simp [hcode, HolFiniteMapExact.empty] at he),
        hdist, hcode, hcode, hfail⟩
    have he := h1 ⟨(by rw [← hs]; exact hfail), hlocals, hcode, hglobals⟩
    have hm : source.eshapes.map2 (fun entry =>
        Pancake.PanStructs.CompileShapeExact.compileShapeExact
          (Pancake.PanStructs.CompileShapeExact.getNamesExact
            { structs := [], locals := [], globals := [] } (panSimpDeclsHOL code)).structs
          entry.2) = source.eshapes := by
      rw [heshapes]; apply HolFiniteMapExact.ext; rfl
    rw [hm] at he
    rw [← he, ← hs]; exact hfail
  have hdiststruct : ((functionsHOL structCode).map Prod.fst).Nodup := by
    dsimp only [structCode]
    rw [functionNamesStructsCompileTopHOL, functionNamesCompileProgHOL]; exact hdist
  obtain ⟨mainBody, mainShape, hmain⟩ := semanticsDeclsHasMainPanToWordHOL source start structCode
    ⟨hcode, hdiststruct, hstructnf⟩
  have hpanSize : sizeOfEidsHOL panCode < 2 ^ width := by
    dsimp only [panCode]
    rw [sizeOfEidsCompileTopHOL structCode start [] mainBody mainShape hmain]
    dsimp only [structCode]
    rw [sizeOfEidsStructsCompileEqHOL, sizeOfEidsHOL_panSimpDeclsHOL_eq]
    exact heids
  have hmf : (crepToLoopMakeFuncsExactHOL (compileProgDeclsHOLW panCode)).lookup start =
      some (firstLoopName, 0) :=
    flookupMakeFuncsMainHOL structCode start mainBody mainShape hmain
  have htop' : globalState.topAddr = globalState.baseAddr + (2 : BitVec width) * heapLen := by
    change source.topAddr + panBytesInWord width * BitVec.ofNat width globalsSize = _
    rw [htop]
    exact BitVec.sub_add_cancel _ _
  have hcodeWord : target.code = sptFromAList
      (loopToWordCompileProgHOL (compileProgHOLExact arch (compileProgDeclsHOLW panCode))) := by
    simpa [panToWordCompileProgHOL, panCode, structCode, hstart, loopToWordCompileHOL] using htcode
  obtain ⟨T, hevT, hresT, hioT⟩ := pan_simp_structs_globals_clocked_sim
    source target code start globalsSize hfail hdist hcode hlocals hglobals heshapes
    hsize halloc halign hdim hmem stCtxt s_decls hst hev_decls k res_src s_src_post hev_call hne_src_err
  rcases hev_pan : PanSemStateFiniteExact.evaluateHOLFiniteState { T with clock := k + 1 }
      (.call none start [] : ProgHOL width) with ⟨res_pan, s_pan_post⟩
  have hres_pan : res_pan = convertResHOL res_src := by
    rw [hev_pan] at hresT; exact hresT
  have hio_pan : s_pan_post.ffi.ioEvents = s_src_post.ffi.ioEvents := by
    rw [hev_pan] at hioT; exact hioT
  have hclass_conv : panEntryClass (convertResHOL res_src) = panEntryClass res_src := by
    rcases res_src with _ | (_ | _ | _ | _ | _ | _ | _) <;>
      simp [convertResHOL, panEntryClass]
  have hne_pan : panEntryClass res_pan ≠ .RunError := by
    rw [hres_pan, hclass_conv]
    exact hne_src
  obtain ⟨k', t_word, res_word, hrun_word, hio_word, hclass_word, hcost_word⟩ :=
    pan_to_crep_to_word_clocked_sim globalState T target arch panCode start heapLen
      hnolabels hstart hmdomain hshdomain hbe hffi hcurrheap hheaplen htop' rfl
      hcode hglobals hlocals heshapes hcodeWord hloc0 hdim
      (allDistinctCompileTopHOL start structCode hdiststruct)
      (compileTopLocalisedHOL structCode start)
      (by apply List.all_eq_true.mpr
          intro d hd
          rcases PanGlobalsCompileDecsStructural.compile_top_only_functions_or_exnsHOL structCode start d hd with h | h <;> simp [h])
      hpanSize hmf hglobalnf hevT (k + 1) res_pan s_pan_post hev_pan hne_pan
  refine ⟨k', t_word, res_word, hrun_word, ?_, ?_, hcost_word⟩
  · rw [hio_word, hio_pan]
  · rw [hclass_word, hres_pan, hclass_conv]


theorem pan_to_word_affine_notTimeOut {width : Nat} [NeZero width] {C σ : Type}
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
      {target with clock := (frontBudget code start + 1) * k + (frontBudget code start + 4)}).1 ≠
      some .timeOut := by
  obtain ⟨extra,post,result,run,_,hclass,hbound⟩ :=
    pan_to_word_clocked_sim source target arch code start globalsSize heapLen h
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
  change (WordSemStateFiniteExact.evaluate _ {target with clock := budget}).1 ≠ _
  rw [lifted]
  exact hnt

#print axioms pan_to_word_affine_notTimeOut

#print axioms pan_to_word_clocked_sim

end InitECandidate.Solver.Wave8Stage.FrontendCostTransfer
