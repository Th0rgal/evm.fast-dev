import InitECandidate.Proofs.BoundedStackToLab
import Flapjack.Pancake.LoopToWord.Proofs.StateRelImpSemantics
import Flapjack.Pancake.CrepToLoop.Proofs.StateRelImpSemantics
import Flapjack.Pancake.Proofs.PanToCrep.StateRelImpSemanticsTop
import Flapjack.Pancake.Proofs.PanToWord.StateRelImpSemantics

namespace InitE
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open Flapjack.LoopToWord.CompileCorrect

/-- Clock-preserving `LoopToWord` simulation: at any clock `k`, a non-error entry call
on `s` (with `sptIsEmpty s.locals`) produces a `WordSem` entry call on `t` at the **same**
clock `k` (`extra = 0`) with `resultCase` and identical FFI state. -/
theorem loop_to_word_clocked_agree {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (start k : Nat)
    (res : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (s1 : LoopSemStateFiniteExact width F)
    (hsr : loopToWordStateRelHOLExact s t)
    (hemp : sptIsEmpty s.locals = true)
    (hdim : goodDimindex width)
    (hret : sptLookup 0 t.locals = some (WordLocW.loc 1 0))
    (hev : LoopSemStateFiniteExact.evaluate
      (.call none (some start) [] none : HolLoopProg width) { s with clock := k } = (res, s1))
    (hne : res ≠ some .error) :
    ∃ t1 res1,
      WordSemStateFiniteExact.evaluate
        (.call none (some start) [0] none : WordLangProgHOL (BitVec width))
        { t with clock := k } = (res1, t1) ∧
      t1.ffi = s1.ffi ∧
      resultCase (makeCtxtHOL 2 [] .ln) (WordLocW.loc 1 0) { t with clock := k } res s1 res1 t1 := by
  have hloc : s.locals = .ln := by
    cases h : s.locals <;> simp_all [sptIsEmpty]
  have hlocals : LoopToWord.localsRelHOL (makeCtxtHOL 2 [] .ln)
      ({ s with clock := k } : LoopSemStateFiniteExact width F).locals
      ({ t with clock := k } : WordSemStateFiniteExact width C F).locals := by
    show LoopToWord.localsRelHOL _ s.locals t.locals
    rw [hloc]
    exact LoopToWord.localsRelHOLMkCtxtLn 2 [] _ ⟨by decide, by decide⟩
  obtain ⟨t1, res1, hrun, hffi, hrc⟩ :=
    compileCorrect (C := C) (.call none (some start) [] none) { s with clock := k } res s1
      { t with clock := k } (makeCtxtHOL 2 [] .ln) (WordLocW.loc 1 0) (0, 0)
      ⟨hev, hne, loopToWordStateRelWithClockHOLExact s t k hsr, hlocals, hret, hdim,
        by simp [wordSemIsWordLoc], by intro x hx; simp [accVarsHOL, sptMem, sptDomain] at hx⟩
  have hcomp : (LoopToWord.compHOL (makeCtxtHOL 2 [] .ln)
      (.call none (some start) [] none : HolLoopProg width) (0, 0)).1 =
      .call none (some start) [0] none := by simp [LoopToWord.compHOL]
  rw [hcomp] at hrun
  exact ⟨t1, res1, hrun, hffi, hrc⟩

/-- Clocked `CrepToLoop` simulation: at any clock `k`, a non-error entry call on `s`
produces a `LoopSem` entry call on `t` at clock `k + k'` with mapped result
`resultToLoop res` and `crepToLoopStateRelExact s1 t1` (which includes `s1.ffi = t1.ffi`). -/
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
      s1.ffi = t'.ffi := by
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
  obtain ⟨k', res', t', hrun, hsr, hres⟩ :=
    crepToLoopCodeRelEvaluateCallCorrect nctxt s.code t.code start
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
  exact ⟨k', t', hrun', hsr.2.2.2.2.1⟩

/-- Clock-preserving `CrepInline` simulation: at any clock `k`, a non-error entry call
on `s` produces the exact same result and FFI state on `t` at the same clock `k`. -/
theorem crep_inline_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s t : CrepSemHOLState width σ)
    (crep_code : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width))
    (start : MlString)
    (inl_fname : List CrepInlineMapHOLName)
    (k : Nat)
    (hsr : CrepInlineExact.crepInlineStateRelCodeExact s t)
    (hls : CrepInlineExact.crepInlineLocalsStrongRelExact s t)
    (hd : (crep_code.map Prod.fst).Nodup)
    (hs : s.code = alistToFmapCodeExact crep_code)
    (ht : t.code = alistToFmapCodeExact (CrepInlineCanonical.compileInlTopHOLExact inl_fname crep_code))
    (hne : (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ≠ some .error) :
    (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).1 =
      (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).1 ∧
    (evalCrepSemHOLProgExact { t with clock := k } (.call none start [])).2.ffi =
      (evalCrepSemHOLProgExact { s with clock := k } (.call none start [])).2.ffi := by
  let inl_fs := CrepInlineCanonical.alistToFmapHOLExact
    (crep_code.filter fun triple => inl_fname.contains triple.1)
  have ht' : t.code = alistToFmapCodeExact
      (CrepInlineCanonical.compileInlProgHOLExact inl_fs crep_code) := by
    rw [ht, CrepInlineCanonical.compileInlTopHOLExact]
    rw [CrepInlineCanonical.compileInlProgHOLExactWithSupport_eq_compileInlProgHOLExact]
  have hsub : HolFiniteMapExact.submap inl_fs s.code := by
    intro key v h
    rw [hs]
    have hm := flookup_fupdateList_reverse_mem' _ key v h
    exact flookup_fupdateList_reverse_of_mem crep_code key v hd
      (List.mem_filter.mp hm).1
  have hci := CrepInlineStateRelImpSemantics.codeInl_of_alist s t crep_code inl_fs hd hs ht'
  exact CrepInlineStateRelImpSemantics.entry_agree s t start inl_fs hsr hls hsub hci k hne

/-- Clock-preserving `PanToCrep` (pre-inline) simulation: at any clock `k`, a non-error
`PanSem` entry call on `s` produces a `CrepSem` entry call on `t` at the **same** clock `k`
(`extra = 0`) with matching entry classification (`panEntryClass`) and identical FFI state. -/
theorem pan_to_crep_clocked_agree {width : Nat} [NeZero width] {σ : Type}
    (s : PanSemStateFiniteExact width σ) (t : CrepSemHOLState width σ)
    (pan_code : List (DeclHOL width)) (start : MlS) (k : Nat)
    (res : Option (PanSemResultExact width)) (s1 : PanSemStateFiniteExact width σ)
    (hsr : panToCrepStateRelFiniteExact s t)
    (hdist : ((functionsHOL pan_code).map Prod.fst).Nodup)
    (hscode : s.code = HolFiniteMapExact.empty.updateList (functionsHOL pan_code).reverse)
    (htcode : t.code = HolFiniteMapExact.empty.updateList (compileToCrepExactHOLW pan_code).reverse)
    (hloc : s.locals = HolFiniteMapExact.empty)
    (hlocal : ∀ entry ∈ functionsHOL pan_code, localisedProgHOL entry.2.2.1 = true)
    (hsize : sizeOfEidsHOL pan_code < 2 ^ width)
    (hdom : ∀ key, (s.eshapes.lookup key).isSome =
      ((getEidsFromDeclsHOL pan_code).lookup key).isSome)
    (hev : PanSemStateFiniteExact.evaluateHOLFiniteState { s with clock := k }
      (.call none start [] : ProgHOL width) = (res, s1))
    (hne : res ≠ some .error) :
    ∃ res1 t1,
      evalCrepSemHOLProgExact { t with clock := k }
        (.call none start [] : CrepProgHOL width) = (res1, t1) ∧
      t1.ffi = s1.ffi ∧
      (match res1 with
       | some .timeOut => .Incomplete
       | some (.finalFfi e) => .CompleteResult (HolOutcome.ffiOutcome e)
       | some (.return _) => .CompleteResult HolOutcome.success
       | _ => .RunError) = panEntryClass res := by
  let ctxt : PanToCrepContextExact width :=
    mkCtxtExactHOL HolFiniteMapExact.empty (makeFuncsExactHOL (functionsHOL pan_code)) 0
      (getEidsFromDeclsHOL pan_code)
  have hsr' : panToCrepStateRelFiniteExact ({ s with clock := k } : PanSemStateFiniteExact width σ)
      ({ t with clock := k } : CrepSemHOLState width σ) := by
    obtain ⟨h1, h2, h3, h4, h5, _, h7, h8, h9, h10⟩ := hsr
    exact ⟨h1, h2, h3, h4, h5, rfl, h7, h8, h9, h10⟩
  have hcode : codeRelExactHOLW ctxt ({ s with clock := k } : PanSemStateFiniteExact width σ).code
      ({ t with clock := k } : CrepSemHOLState width σ).code := by
    show codeRelExactHOLW ctxt s.code t.code
    rw [hscode, htcode]
    exact mkCtxtCodeImpCodeRelExactHOLW pan_code hdist hlocal
  have hexcp : panToCrepExcpRelFiniteExact ctxt.eids
      ({ s with clock := k } : PanSemStateFiniteExact width σ).eshapes :=
    getEidsImpExcpRelExact s.eshapes pan_code ⟨hsize, hdom⟩
  have hlocals : panToCrepLocalsRelFiniteExact ctxt
      ({ s with clock := k } : PanSemStateFiniteExact width σ).locals
      ({ t with clock := k } : CrepSemHOLState width σ).locals := by
    show panToCrepLocalsRelFiniteExact ctxt s.locals t.locals
    rw [hloc]
    exact mkCtxtImpLocalsRelExact _ _ _
  obtain ⟨res1, t1, hrun, hsr1, _, _, hres⟩ :=
    pcCompileCorrect (.call none start []) { s with clock := k } res s1 { t with clock := k } ctxt
      ⟨hev, hne, hsr', hcode, hexcp, hlocals, by simp [localisedProgHOL, everyExpListHOL]⟩
  have hcomp : compileProgExactHOLW ctxt (.call none start [] : ProgHOL width) =
      (.call none start [] : CrepProgHOL width) := by
    simp [compileProgExactHOLW, compileCallNoReturnExactHOLW, compileExpExactHOLWList]
  rw [hcomp] at hrun
  refine ⟨res1, t1, hrun, hsr1.2.2.2.2.2.2.2.1.symm, ?_⟩
  rcases res with _ | (_ | _ | _ | _ | _ | _ | _) <;> simp only at hres <;>
    (try split at hres) <;> simp_all [panEntryClass]

#print axioms loop_to_word_clocked_agree
#print axioms crep_to_loop_clocked_sim
#print axioms crep_inline_clocked_agree
#print axioms pan_to_crep_clocked_agree

end InitE
