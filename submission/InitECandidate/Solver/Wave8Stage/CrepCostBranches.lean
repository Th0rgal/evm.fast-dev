import InitECandidate.Solver.Wave8Stage.CrepCostLeaf
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.Dec
import Flapjack.Pancake.CrepToLoop.Proofs.NcompileCorrect

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CrepCostBranches
open Flapjack CrepExpressionClock CrepSourceCost CrepCostLeaf
open LoopSemStateFiniteExact
open Pancake.CrepToLoop.Proofs.NCompileCorrect

theorem compCorrectDec {width : Nat} [NeZero width] {σ : Type} :
    ∀ (name : Nat) (e : CrepExpHOL width) (body : CrepProgHOL width)
      (v1 : CrepSemHOLState width σ),
      (∀ value, evalCrepSemHOLExp v1 e = some value →
        PropertyB body
          { v1 with locals := v1.locals.updateEq (name, value) }) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.dec name e body) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.dec name e body))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = resultToLoop res ∧
        localsResultRel ctxt l res s1 t1 ∧ ck ≤ sourceCost (.dec name e body) v1 := by
  intro name e body v1 ih res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_dec_holShape] at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
      simp only [hev, Prod.mk.injEq] at he
      exact absurd he.1.symm hne
  | some value =>
      simp only [hev] at he
      let sourceBody : CrepSemHOLState width σ :=
        { v1 with locals := v1.locals.updateEq (name, value) }
      cases hBody : evalCrepSemHOLProgExact sourceBody body with
      | mk bodyResult bodyState =>
        rw [hBody] at he
        simp only [Prod.mk.injEq] at he
        rcases he with ⟨hResult, hFinal⟩
        have hBodyEval : evalCrepSemHOLProgExact sourceBody body = (bodyResult, bodyState) := hBody
        rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with
          ⟨codePrefix, compiledValue, temporary, nextLive⟩
        obtain ⟨prefixClock, prefixState, hPrefix, hValue, hPrefixState,
          hPrefixMem, hPrefixGlobals, hPrefixCode, hPrefixLocals, hPrefixBound⟩ :=
          compExp_preserves_eval_bounded v1 e value t ctxt (ctxt.vmax + 1) l
            codePrefix compiledValue temporary nextLive
            ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
        obtain ⟨hNoContext, hTempBound, hNextLive⟩ :=
          compile_exp_out_rel ctxt (ctxt.vmax + 1) l e codePrefix compiledValue temporary nextLive hC
        have hLiveNext : ∀ k, sptMem k l → sptMem k nextLive := by
          intro k hk
          rw [hNextLive]
          exact cut_sets_union_domain_subset _ l hNoContext k hk
        have hLocalsBefore : crepToLoopLocalsRelExact ctxt l v1.locals prefixState.locals := by
          refine ⟨hPrefixLocals.1, hPrefixLocals.2.1, ?_, ?_⟩
          intro k hk
          exact hPrefixLocals.2.2.1 k (hLiveNext k hk)
          intro key val hval
          obtain ⟨n, hmap, hmem, _⟩ := hl.2.2.2 key val hval
          obtain ⟨n', hmap', _, hslot⟩ := hPrefixLocals.2.2.2 key val hval
          have hn : n' = n := Option.some.inj (hmap'.symm.trans hmap)
          subst n'
          exact ⟨n, hmap', hmem, hslot⟩
        have hFresh : ctxt.vmax < temporary := by omega
        let bodyCtxt : CrepToLoopContextExact :=
          { ctxt with vars := ctxt.vars.updateEq (name, temporary), vmax := temporary }
        let bodyLive : NumSet := sptInsert temporary () l
        let targetBody : LoopSemStateFiniteExact width σ :=
          LoopSemStateFiniteExact.setVar temporary (wlabWlocExact value) prefixState
        have hBodyLocals : crepToLoopLocalsRelExact bodyCtxt bodyLive
            sourceBody.locals targetBody.locals := by
          have hw : (wlabWlocExact : HolWordLab width → WordLocW width) = wlabWlocHOL := by
            funext v
            cases v
            rfl
          have hEntered := crepToLoopNcompileDecLocalsEnter ctxt l v1.locals prefixState.locals
            name temporary value hLocalsBefore hFresh
          rw [← hw] at hEntered
          simpa [sourceBody, targetBody, bodyLive, bodyCtxt, CrepSemHOLState.setVar,
            LoopSemStateFiniteExact.setVar] using hEntered
        have hBodyState : crepToLoopStateRelExact sourceBody targetBody := by
          simpa [sourceBody, targetBody, crepToLoopStateRelExact,
            LoopSemStateFiniteExact.setVar] using hPrefixState
        have hBodyMem : crepToLoopMemRelHOLExact sourceBody.memory targetBody.memory
            sourceBody.memaddrs := by
          simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixMem
        have hBodyGlobals : crepToLoopGlobalsRelHOLExact sourceBody.globals targetBody.globals := by
          simpa [sourceBody, targetBody, LoopSemStateFiniteExact.setVar] using hPrefixGlobals
        have hBodyCode : crepToLoopCodeRelExact bodyCtxt sourceBody.code targetBody.code := by
          simpa [sourceBody, targetBody, bodyCtxt, crepToLoopCodeRelExact,
            LoopSemStateFiniteExact.setVar] using hPrefixCode
        have hBodyNotError : bodyResult ≠ some .error := by
          intro herr
          apply hne
          rw [← hResult]
          exact herr
        let bodyIH := ih value hev
        obtain ⟨bodyClock, targetResult, targetFinal, hTargetBodyEval,
          hFinalStateBody, hFinalMemBody, hFinalGlobalsBody, hFinalCodeBody,
          hResultBody, hLocalsBody, hBodyBound⟩ :=
          bodyIH bodyResult bodyState targetBody bodyCtxt bodyLive
            hBodyEval hBodyNotError hBodyState hBodyMem hBodyGlobals
              hBodyCode hBodyLocals
        have hCompile : compileHOLExact ctxt l (.dec name e body) =
            .seq (loopNestedSeqHOL codePrefix)
              (.seq (.assign temporary compiledValue)
                (compileHOLExact bodyCtxt bodyLive body)) := by
          rw [compileHOLExact, hC]
        have hPrefixLift : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL codePrefix)
            { t with clock := t.clock + (prefixClock + bodyClock) } =
              (none, { prefixState with clock := prefixState.clock + bodyClock }) := by
          have hLift := LoopSemStateFiniteExact.evaluate_add_clock_eq
            (loopNestedSeqHOL codePrefix) { t with clock := t.clock + prefixClock }
            none prefixState bodyClock hPrefix (by simp)
          simpa [Nat.add_assoc] using hLift
        have hAssignEval : LoopSemStateFiniteExact.evaluate (.assign temporary compiledValue)
            { prefixState with clock := prefixState.clock + bodyClock } =
              (none, { targetBody with clock := targetBody.clock + bodyClock }) := by
          rw [LoopSemStateFiniteExact.evaluate.eq_3]
          simp [LoopSemStateFiniteExact.eval_upd_clock_eq, hValue, targetBody,
            LoopSemStateFiniteExact.setVar]
        have hRun : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.dec name e body))
            { t with clock := t.clock + (prefixClock + bodyClock) } = (targetResult, targetFinal) := by
          rw [hCompile]
          simp only [LoopSemStateFiniteExact.evaluate_seq, hPrefixLift]
          rw [hAssignEval]
          exact hTargetBodyEval
        have hResultFinal : targetResult = resultToLoop res := by
          calc
            targetResult = resultToLoop bodyResult := hResultBody
            _ = resultToLoop res := by rw [← hResult]
        have hSourceFinalLocals : s1.locals =
            bodyState.locals.resVarEq (name, v1.locals.lookup name) := by
          have hLocalsEq := congrArg (fun state : CrepSemHOLState width σ => state.locals) hFinal
          simpa [sourceBody] using hLocalsEq.symm
        have hMakePreserve : UnassignedGoodRes targetResult → ∀ n old,
            ctxt.vars.lookup name = some n → v1.locals.lookup name = some old →
              sptLookup n targetFinal.locals = sptLookup n prefixState.locals := by
          intro hGood n old hname hOld
          have hmax := hLocalsBefore.2.1 name n hname
          have hneTmp : n ≠ temporary := by omega
          obtain ⟨mapped, hmap, hmem, hslot⟩ :=
            hLocalsBefore.2.2.2 name old hOld
          have hmapped : mapped = n := Option.some.inj (hmap.symm.trans hname)
          subst mapped
          have hslotTarget : sptLookup n targetBody.locals = some (wlabWlocHOL old) := by
            simpa [targetBody, LoopSemStateFiniteExact.setVar, sptLookup_sptInsert,
              hneTmp, wlabWlocExact, wlabWlocHOL] using hslot
          have hNotAssigned : n ∉ holLoopAssignedVars
              (compileHOLExact bodyCtxt bodyLive body) := by
            apply not_mem_context_assigned_mem_gt bodyCtxt bodyLive body n
            refine ⟨hBodyLocals.2.1, ?_, ?_⟩
            · intro var mapped hlookup
              by_cases hvar : var = name
              · subst var
                have hmapped : temporary = mapped := by
                  simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL] using hlookup
                omega
              · have hlookupOld : ctxt.vars.lookup var = some mapped := by
                  simpa [bodyCtxt, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL, hvar] using hlookup
                intro heq
                have hsame := hLocalsBefore.1 name var n mapped hname hlookupOld heq
                exact hvar hsame.symm
            · have hnle : n ≤ ctxt.vmax := hmax
              have hnleBody : n ≤ bodyCtxt.vmax := by
                simpa [bodyCtxt] using (Nat.le_trans hnle (Nat.le_of_lt hFresh))
              exact hnleBody
          have hLive : (sptLookup n bodyLive).isSome = true := by
            exact (sptMem_sptInsert n temporary () l).mpr (Or.inr hmem)
          have hSurvives : survivesHOLExact n
              (compileHOLExact bodyCtxt bodyLive body) = true :=
            member_cutset_survives_comp_prog bodyCtxt bodyLive body n hLive
          have hRunPreserved := unassigned_vars_evaluate_same
            (compileHOLExact bodyCtxt bodyLive body)
            { targetBody with clock := targetBody.clock + bodyClock }
            targetResult targetFinal n (wlabWlocHOL old)
            ⟨hTargetBodyEval, hGood, by
              simpa [targetBody, LoopSemStateFiniteExact.setVar] using hslotTarget,
              hNotAssigned, hSurvives⟩
          have hslotInitial : sptLookup n prefixState.locals = some (wlabWlocHOL old) := hslot
          calc
            sptLookup n targetFinal.locals = sptLookup n targetBody.locals := hRunPreserved
            _ = sptLookup n prefixState.locals := hslotTarget.trans hslotInitial.symm
        have hFinalLocals : localsResultRel ctxt l res s1 targetFinal := by
          cases res with
          | none =>
              have hGood : UnassignedGoodRes targetResult := by
                simp [hResultFinal, resultToLoop, UnassignedGoodRes]
              have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                  bodyState.locals targetFinal.locals := by
                  simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
              exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                (hMakePreserve hGood)
          | some result =>
              cases result with
              | «break» n =>
                  have hGood : UnassignedGoodRes targetResult := by
                    simp [hResultFinal, resultToLoop, UnassignedGoodRes]
                  have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                      bodyState.locals targetFinal.locals := by
                    simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
                  exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                    v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                    hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                    (hMakePreserve hGood)
              | «continue» n =>
                  have hGood : UnassignedGoodRes targetResult := by
                    simp [hResultFinal, resultToLoop, UnassignedGoodRes]
                  have hBodyLocalsFinal : crepToLoopLocalsRelExact bodyCtxt bodyLive
                      bodyState.locals targetFinal.locals := by
                    simpa [localsResultRel, hResultBody, hResult] using hLocalsBody
                  exact crepToLoopNcompileDecLocalsRestore ctxt bodyCtxt l name temporary
                    v1.locals bodyState.locals s1.locals prefixState.locals targetFinal.locals
                    hLocalsBefore hBodyLocalsFinal (by rfl) hFresh hSourceFinalLocals
                    (hMakePreserve hGood)
              | «return» _ => trivial
              | exception _ => trivial
              | timeOut => trivial
              | finalFfi _ => trivial
              | error =>
                  exfalso
                  apply hne
                  rw [← hResult]
        refine ⟨prefixClock + bodyClock, targetResult, targetFinal, hRun, ?_, ?_, ?_, ?_, hResultFinal,
          hFinalLocals, by
            simpa [sourceCost, hev, sourceBody] using Nat.add_le_add hPrefixBound hBodyBound⟩
        · rw [← hFinal]
          simpa [crepToLoopStateRelExact] using hFinalStateBody
        · rw [← hFinal]
          simpa using hFinalMemBody
        · rw [← hFinal]
          simpa using hFinalGlobalsBody
        · rw [← hFinal]
          simpa [crepToLoopCodeRelExact, bodyCtxt] using hFinalCodeBody


theorem compCorrectIf {width : Nat} [NeZero width] {σ : Type} :
    ∀ (e : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (v1 : CrepSemHOLState width σ),
      (∀ w, evalCrepSemHOLExp v1 e = some (.word w) →
        PropertyB (if w ≠ 0 then c1 else c2) v1) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.ite e c1 c2) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat) (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.ite e c1 c2))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = resultToLoop res ∧
        localsResultRel ctxt l res s1 t1 ∧ ck ≤ sourceCost (.ite e c1 c2) v1 := by
  intro e c1 c2 v1 ih res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
    simp only [hev, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some x =>
  cases x with
  | word w =>
  simp only [hev] at he
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l, h1bound⟩ :=
    compExp_preserves_eval_bounded v1 e (.word w) t ctxt (ctxt.vmax + 1) l np le tmp nl
      ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  -- `st with locals := insert tmp (Word w) st.locals` satisfies `locals_rel ctxt l`
  have hl' : crepToLoopLocalsRelExact ctxt l v1.locals
      (LoopSemStateFiniteExact.setVar tmp (.word w) st).locals := by
    refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
    · have hnl : sptDomain nl k := hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
      exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k hnl))
    · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
      obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
      have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
      subst hnn
      have hle := h1l.2.1 vn n' hn1'
      refine ⟨n', hn1', hn2, ?_⟩
      simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
      rw [if_neg (by omega)]
      exact hn3'
  obtain ⟨ck', res1, t1, h2, h2s, h2m, h2g, h2c, h2r, h2l, h2bound⟩ :=
    ih w hev res s1 (LoopSemStateFiniteExact.setVar tmp (.word w) st) ctxt l
      he hne h1s h1m h1g h1c hl'
  have hbound : ck + (ck' + 1) ≤ sourceCost (.ite e c1 c2) v1 := by
    have hbranch : sourceCost (if w ≠ 0 then c1 else c2) v1 =
        if w = 0 then sourceCost c2 v1 else sourceCost c1 v1 := by
      by_cases hw : w = 0 <;> simp only [hw, ne_eq, not_true_eq_false, not_false_eq_true, if_true, if_false]
    rw [hbranch] at h2bound
    simp only [sourceCost, hev]
    omega
  have hcomp : compileHOLExact ctxt l (.ite e c1 c2) =
      loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width))
           (compileHOLExact ctxt l c1) (compileHOLExact ctxt l c2) l]) := by
    rw [compileHOLExact, hC]
  rw [hcomp]
  -- the `Assign tmp le; If NotEqual tmp (Imm 0w) ...` tail from any clock extension
  have htail : ∀ k, LoopSemStateFiniteExact.evaluate
      (loopNestedSeqHOL
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width))
           (compileHOLExact ctxt l c1) (compileHOLExact ctxt l c2) l])
      { st with clock := st.clock + k } =
      LoopSemStateFiniteExact.cutRes l
        (LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
          { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + k }) := by
    intro k
    have hle : LoopSemStateFiniteExact.eval { st with clock := st.clock + k } le =
        some (.word w) := by
      rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v
    simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
    simp only [LoopSemStateFiniteExact.evaluate, hle]
    simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
      LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hw : w = 0
    · simp only [hw, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false,
        ne_eq, not_true_eq_false]
      split <;> rename_i h <;> exact h.symm
    · have hb : (w == 0) = false := by simpa using hw
      simp only [hb, Bool.not_false, if_true, ne_eq, hw, not_false_eq_true]
      split <;> rename_i h <;> exact h.symm
  have h1k : ∀ k, LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np)
      { t with clock := t.clock + (ck + k) } = (none, { st with clock := st.clock + k }) := by
    intro k
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
    simpa [Nat.add_assoc] using this
  have h2' : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
      { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + ck' } =
        (res1, t1) := h2
  cases res with
  | none =>
    have hr1 : res1 = none := by simpa [resultToLoop] using h2r
    subst hr1
    have h2l' : crepToLoopLocalsRelExact ctxt l s1.locals t1.locals := h2l
    have h2k : LoopSemStateFiniteExact.evaluate
        (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
        { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + (ck' + 1) } =
          (none, { t1 with clock := t1.clock + 1 }) := by
      have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h2' (by simp)
      simpa [Nat.add_assoc] using this
    have hsub : LoopSemStateFiniteExact.sptSubsetLive l t1.locals := h2l'.2.2.1
    have hcut : LoopSemStateFiniteExact.cutRes l (none, { t1 with clock := t1.clock + 1 }) =
        (none, { t1 with locals := sptInter t1.locals l }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l { t1 with clock := t1.clock + 1 } hsub]
      simp [LoopSemStateFiniteExact.decClock]
    refine ⟨ck + (ck' + 1), none, { t1 with locals := sptInter t1.locals l }, ?_, h2s, h2m,
      h2g, h2c, rfl, ?_, hbound⟩
    · rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ (h1k (ck' + 1)),
        htail, h2k, hcut]
    · refine ⟨h2l'.1, h2l'.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
      · have hk' : (sptLookup k l).isSome := hk
        show (sptLookup k (sptInter t1.locals l)).isSome
        rw [sptLookup_sptInter, if_pos hk']
        exact hsub k hk
      · obtain ⟨n, hn1, hn2, hn3⟩ := h2l'.2.2.2 vn val hval
        have hnl : (sptLookup n l).isSome := hn2
        refine ⟨n, hn1, hn2, ?_⟩
        show sptLookup n (sptInter t1.locals l) = _
        rw [sptLookup_sptInter, if_pos hnl]
        exact hn3
  | some r =>
    obtain ⟨x, hx⟩ : ∃ x, res1 = some x := by
      cases r <;> simp only [resultToLoop] at h2r <;> exact ⟨_, h2r⟩
    refine ⟨ck + ck', res1, t1, ?_, h2s, h2m, h2g, h2c, h2r, h2l, by omega⟩
    rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ (h1k ck'), htail, h2', hx]
    rfl


#print axioms compCorrectDec
#print axioms compCorrectIf

end InitECandidate.Solver.Wave8Stage.CrepCostBranches
