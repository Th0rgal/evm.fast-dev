import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallR32

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

local notation "evmR" => R11Shards.OpDispatchSpec.evmR
/-! #R#32 slot 6b: child-push `generic_call` leaf, part 1 (combinator + the
`op_delegatecall` / `op_staticcall` walks)

This file rebuilds the `op_delegatecall` and `op_staticcall` suffix walks of the
compiled Group 10 tails under the true child-push contract
`callSpec_generic_call_r32` (see `Group10CallR32.lean`).  The key combinator is
`ccA_decCall_childCall_r32`: a `decCall ... "generic_call" args cont` node with an
arbitrary continuation `cont`.  When the child-push contract reports a nonzero
`started` (a child frame was pushed, the chain grew by one), the continuation
cannot raise an `EvmErr` (given by `hnoraise`, discharged by
`noEvmErr_afterCall_r32` for the standard call-handler suffix
`ite (started == 0) (pc_add 1) skip; return 0`); when the contract reports
`started == 0` (depth cap, chain unchanged) or the callee itself errors, the
chain is kept, so the enclosing `ChildContinuationA` boundary holds with the
error branch keeping the chain depth as required. -/

/-! ## The child-push `decCall` combinator -/

/-- After `generic_call` returns a nonzero word (the push case), the opcodes' tail
`ite (started = 0) (pc_add 1) skip; return 0` cannot produce `EvmErr`: the condition
evaluates false, so the tail is `skip; return 0`. -/
theorem noEvmErr_afterCall_r32 {F : Type} (t' : PanSemStateFiniteExact 64 F)
    (w : BitVec 64)
    (hst : t'.locals.lookup (ofString "started") = some (.val (.word w)))
    (hw : w ≠ 0) :
    ¬ IsEvmErr ((evaluateHOLFiniteState t'
      (.seq (.ite (.cmp Cmp.equal (.var .local (ofString "started")) (.const 0#64))
          (.call (some (none, none)) (ofString "pc_add") [ExpHOL.const 1#64]) .skip)
        (.return (.const 0#64)))).1) := by
  rintro ⟨ev, he⟩
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at he
  have hcond : @evalHOLExact 64 F _ t'.toExact
      (fun a => Classical.propDecidable (t'.memaddrs a))
      (.cmp Cmp.equal (.var .local (ofString "started")) (.const 0#64)) =
      some (.val (.word 0#64)) := by
    simp only [evalHOLExact, hst, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hwz : w = 0#64
    · exact absurd hwz hw
    · simp [hwz]
  rw [hcond] at he
  dsimp only at he
  have hzz : (0#64 : BitVec 64) = 0 := by decide
  rw [if_pos hzz, evaluateHOLFiniteState_skip] at he
  dsimp only at he
  rw [evaluateHOLFiniteState_return] at he
  simp only [evalHOLExact] at he
  split at he
  · simp at he
  · simp at he

/-- `ccA_decCall_g10` for a child-push callee: on the callee's own `EvmErr` its chain is
kept (the spec's error case), and after a nonzero return the continuation cannot raise
(`hnoraise`), so `ChildContinuationA`'s error-depth obligation holds; the return case needs
no chain condition at all. -/
theorem ccA_decCall_childCall_r32 {F : Type} {P : PanSemStateFiniteExact 64 F → Prop}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmChildPushSpecA (fun _ => True) (fun s _ post => LocFrame s post) fname)
    (hnoraise : ∀ (t' : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      t'.locals.lookup nm = some (.val (.word w)) → w ≠ 0 →
      ¬ IsEvmErr ((evaluateHOLFiniteState t' cont).1))
    (hcont : ChildContinuationA (F := F) (fun _ => True) cont) :
    ChildContinuationA P (.decCall nm sh fname args cont) := by
  intro t hc hi hw hp hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
      fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
        fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup fname params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) :=
          localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := R11Shards.OpDispatchSpec.evm_congr (s := t)
          (t := (callEntryStateHOLFinite t callee : PanSemStateFiniteExact 64 F)) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
                evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
                LocFrame (callEntryStateHOLFinite t callee) cpost ∧
                ((v = .val (.word 0#64) ∧
                    evmChain cpost = evmChain (callEntryStateHOLFinite t callee)) ∨
                  ((evmChain cpost).length =
                      (evmChain (callEntryStateHOLFinite t callee)).length + 1 ∧
                    ∃ w : BitVec 64, w ≠ 0#64 ∧ v = .val (.word w)))) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
                evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
                evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce trivial ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none =>
          refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
            fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              dsimp only at hnt ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hR_cp, -, hcorr⟩ := (hQ (by simp)).1 v rfl
              have hcode_res : ((setVarHOLFinite nm v { cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F)).code = originalRuntimeCode := hmeta.trans hc
              have hi_res : EvmInv (setVarHOLFinite nm v { cpost with locals := t.locals }) :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_res : Group10.HeadMemChainWF (setVarHOLFinite nm v { cpost with locals := t.locals }) :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_res := R11Shards.OpDispatchSpec.evm_congr (s := cpost)
                (t := (setVarHOLFinite nm v { cpost with locals := t.locals } :
                  PanSemStateFiniteExact 64 F)) rfl rfl
              have hR_res : evmR (setVarHOLFinite nm v { cpost with locals := t.locals }) ≤
                  evmR t := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp
              obtain ⟨hret, herr⟩ := hcont (setVarHOLFinite nm v { cpost with locals := t.locals })
                hcode_res hi_res hw_res trivial hnt
              have hc_fin := R11Shards.OpDispatchSpec.evm_congr
                (s := ((evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont).2 :
                  PanSemStateFiniteExact 64 F))
                (t := ({ (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont).2 with
                  locals := HolFiniteMapExact.resVarEq
                    (evaluateHOLFiniteState (setVarHOLFinite nm v { cpost with locals := t.locals }) cont).2.locals
                    (nm, t.locals.lookup nm) } : PanSemStateFiniteExact 64 F)) rfl rfl
              refine ⟨fun hr => ?_, fun he => ?_⟩
              · obtain ⟨hinv, hle⟩ := hret hr
                refine ⟨⟨?_, ?_⟩, ?_⟩
                · exact localsFree_evmInv _ _ _ hinv.1
                · exact Group10.headMemChainWF_locals _ _ _ hinv.2
                · rw [hc_fin.2.1]; exact le_trans hle hR_res
              · obtain ⟨hinv, hdepth, hle⟩ := herr he
                rcases hcorr with ⟨-, hch_cp⟩ | ⟨-, w, hw0, hvw⟩
                · refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
                  · exact localsFree_evmInv _ _ _ hinv.1
                  · exact Group10.headMemChainWF_locals _ _ _ hinv.2
                  · rw [hc_fin.2.2.1, hdepth, hc_res.2.2.1, hch_cp, hc_ce.2.2.1]
                  · rw [hc_fin.2.1]; exact le_trans hle hR_res
                · have hset : (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup nm
                      = some (.val (.word w)) := by
                    have h1 : (setVarHOLFinite nm v { cpost with locals := t.locals }).locals.lookup nm
                        = some v := by
                      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                    rw [h1, hvw]
                  exact absurd he (hnoraise _ w hset hw0)
            · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
                fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              dsimp only at hnt ⊢
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := R11Shards.OpDispatchSpec.evm_congr (s := cpost)
                (t := (cpost.emptyLocalsHOLFinite : PanSemStateFiniteExact 64 F)) rfl rfl
              have hlen_cp : (evmChain cpost).length =
                  (evmChain (callEntryStateHOLFinite t callee)).length := by rw [hch_cp]
              refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h), fun _ => ?_⟩
              exact ⟨⟨hi_el, hw_el⟩, by rw [hc_el.2.2.1, hlen_cp, hc_ce.2.2.1],
                by rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp⟩
            · refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
                fun he => absurd he ?_⟩
              intro hc
              obtain ⟨_, hv⟩ := hc
              injection hv with h'; injection h' with h1 _
              exact heid h1
          | «break» | «continue» | error | finalFfi _ =>
            refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
              fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩

/-! ## `op_delegatecall` under the child-push contract -/

theorem dcExtCodeChain_ccA_r32 {F : Type} (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    @ChildContinuationA F scXQ dcExtCodeProg_g10 := by
  apply ccA_decCall_g10 (Q := scXQ) hW.epsA_ext_code_of
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hgk, _, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
    exact hm32
  apply ccA_decCall_g10 (Q := scXQ) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_decCall_g10 (Q := scXQ) epsA_calculate_message_call_gas
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
    (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
    obtain ⟨hglob, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_congr_g10 hglob "ev"]
    exact hm32
  apply ccA_seq_store_ev_g10 (Q := scXQ) 184 (by decide)
    (hval := fun t v _ hv => eval_op_word_g10 _ _ v hv)
    (hstep := fun t w _ hi _ hp => scXQ_of_updW_g10 184 (by decide) (by decide) hi w hp)
  apply ccA_seq_call_g10 (Q := XShQ_g10) epsA_extend_memory
    (hentry := fun t values body callee rs hc hi hw hp ha hl =>
      memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl)
    (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
      obtain ⟨cw, ebw, hxl, _⟩ := hp
      exact ⟨cw, ebw, hxl⟩)
  apply ccA_dec_g10 (Q := XShQ_g10)
    (hinit := fun t v _ _ hp => xShQ_setvar_g10 (by decide) hp)
  apply ccA_seq_store_ev_g10 (Q := XShQ_g10) 72 (by decide)
    (hval := fun t v _ hv => ⟨(BitVec.ofNat 64 0), eval_const_word_g10 _ v hv⟩)
    (hstep := fun t w _ _ _ hp => xShQ_of_updW_g10 72 w hp)
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_childCall_r32 hgc32
    (hnoraise := fun t' w hl hw => by exact noEvmErr_afterCall_r32 t' w hl hw)
  apply ccA_seq_ite_g10
  · intro t w hcond hw0
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add
      (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial)
      (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
      (ccA_ret_g10 (.const 0#64))
  · intro t hcond
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const 0#64))

theorem dcDlChain_ccA_r32 {F : Type} (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    @ChildContinuationA F scXQ
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
        (ofString "calculate_delegation_cost") [.var .local (ofString "code_address0")]
        (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
          (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
              (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.rfield 2 (.var .local (ofString "dl"))])
              (.call (some (none, none)) (ofString "warm_address")
                [.var .local (ofString "code_address")]))
            .skip)
            dcExtCodeProg_g10))) := by
  apply ccA_decCall_g10 (Q := scXQ) (epsA_cdc_full_g10 hW)
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hpins, _, _⟩ := hQc
    obtain ⟨hev, hm32, _⟩ := hpins v rfl
    refine scXQ_setvar_g10 (by decide) (scXQ_of_pins_g10 hp ?_)
    rw [hev]
    exact hm32
  apply ccA_dec_g10 (Q := scXQ)
    (hinit := fun t v _ _ hp => scXQ_setvar_g10 (by decide) hp)
  apply ccA_seq_ite_g10
  · intro t w _ _
    rw [ccA_seq_seq_assoc_g10]
    apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
    · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
      obtain ⟨hglob, hm32⟩ := hQc
      refine scXQ_of_pins_g10 hp ?_
      rw [globN_congr_g10 hglob "ev"]
      exact hm32
    · apply ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
        (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32
      · exact dcExtCodeChain_ccA_r32 hW hgc32
  · intro t _
    exact ccA_seq_skip_g10 (dcExtCodeChain_ccA_r32 hW hgc32)

theorem dcRest_ccA_r32 {F : Type} (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    @ChildContinuationA F scXQ
      (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "code_address0")])
          .skip)
        (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost") [.var .local (ofString "code_address0")]
          (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
            (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
                (.const (BitVec.ofNat 64 0)))
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                  [.rfield 2 (.var .local (ofString "dl"))])
                (.call (some (none, none)) (ofString "warm_address")
                  [.var .local (ofString "code_address")]))
              .skip)
              dcExtCodeProg_g10)))) := by
  apply ccA_seq_ite_g10
  · intro t w _ _
    exact ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32)
      (dcDlChain_ccA_r32 hW hgc32)
  · intro t _
    exact ccA_seq_skip_g10 (dcDlChain_ccA_r32 hW hgc32)

/-! ### The `op_delegatecall` need chain (nodes 14-16) -/

theorem op_delegatecall_needChain_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 (fun s => scXQ s ∧ AcQ_g10 s) charged
      (.decCall (ofString "need") .one (ofString "add_sat")
        [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "need")])
          cont)) := by
  apply HandlerRunA.decCall (Q := fun s => scXQ s ∧ NdQ_g10 s) epsA_add_sat_ge_g10
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost hi hw hp hargs hlk hi2 hw2 hch hQc
    obtain ⟨hlf, aw, rw, hla, hvw, hle⟩ := hQc
    obtain ⟨acw, hl_ac, hac⟩ := hp.2
    obtain ⟨v0, v1, hv0_ev, hv1_ev, hvals⟩ : ∃ v0 v1,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) = some v0 ∧
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) = some v1 ∧
        values = [v0, v1] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) with _ | v0
      · simp [he0] at hargs
      rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | v1
      · simp [he0, he1] at hargs
      simp only [he0, he1, Option.some.injEq] at hargs
      exact ⟨v0, v1, rfl, rfl, hargs.symm⟩
    subst hvals
    obtain ⟨w0, w1, hv0w, hv1w, hla0, _⟩ := add_sat_args_lookup_g10 hlk
    have hv0_acw : t.locals.lookup (ofString "access_cost") = some (.val (.word w0)) := by
      rw [← hv0w]; exact hv0_ev
    have hw0_acw : w0 = acw := by
      have h := hl_ac.symm.trans hv0_acw
      injection h with h1
      injection h1 with h2
      injection h2 with h3
      exact h3.symm
    have hla' : callee.lookup (ofString "a") = some (.val (.word aw)) := hla
    have haw : aw = w0 := by
      have h := hla'.symm.trans hla0
      injection h with h1
      injection h1 with h2
      injection h2 with h3
    have hle_nat : aw.toNat ≤ rw.toNat := hle
    rw [haw, hw0_acw] at hle_nat
    have h100 : 100 ≤ acw.toNat := by rcases hac with rfl | rfl <;> simp
    refine ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp.1 hlf), rw, ?_, ?_⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl, hvw] | simp [hvw]
    · omega
  apply HandlerRunA.seq_charge_gas_keep32_g10 (Q := scXQ)
    (hpos := fun t w hv _ _ hp => by
      obtain ⟨nw, hlk_n, hbound⟩ := hp.2
      have hev : t.locals.lookup (ofString "need") = some (.val (.word w)) := hv
      rw [hlk_n] at hev
      injection hev with h1
      injection h1 with h2
      injection h2 with h3
      subst h3
      omega)
    (hstep := fun t cpost _ _ hp _ _ _ hm32 _ => scXQ_of_pins_g10 hp.1 hm32)
    (hcont := hcont)

/-! ### The `op_delegatecall` compiled prefix (nodes 10-16) -/

theorem op_delegatecall_prefix2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 scXQ charged
      (.decCall (ofString "warm") .one (ofString "is_warm_address") [.var .local (ofString "code_address0")]
        (.dec (ofString "access_cost") .one (.const (BitVec.ofNat 64 100))
          (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
              (.assign .local (ofString "access_cost") (.const (BitVec.ofNat 64 3000))) .skip)
            (.decCall (ofString "need") .one (ofString "add_sat")
              [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.var .local (ofString "need")]) cont))))) := by
  apply HandlerRunA.decCall (Q := scXQ) epsA_is_warm_address
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply HandlerRunA.dec (Q := fun s => scXQ s ∧ AcQ_g10 s)
    (hinit := fun t v hv _ hp => by
      have hvw : v = .val (.word (BitVec.ofNat 64 100)) := eval_const_word_g10 _ v hv
      subst hvw
      refine ⟨scXQ_setvar_g10 (by decide) hp, (BitVec.ofNat 64 100), ?_, Or.inl rfl⟩
      dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl] | simp)
  apply HandlerRunA.seq_ite_unit
  · intro t w _ _
    apply HandlerRunA.seq_assign_local (Q := fun s => scXQ s ∧ AcQ_g10 s)
      (hasgn := fun t v hv _ hp => by
        have hvw : v = .val (.word (BitVec.ofNat 64 3000)) := eval_const_word_g10 _ v hv
        subst hvw
        refine ⟨scXQ_setvar_g10 (by decide) hp.1, (BitVec.ofNat 64 3000), ?_, Or.inr rfl⟩
        dsimp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos rfl] | simp)
    exact op_delegatecall_needChain_r32 hW hcont
  · intro t _
    exact HandlerRunA.seq_skip (op_delegatecall_needChain_r32 hW hcont)

/-! ### `op_delegatecall` assembly -/

theorem op_delegatecall_run_full_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hW : WorldAccountSpecsA) (hgc32 : callSpec_generic_call_r32) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_delegatecall) :=
  op_delegatecall_prefix1_g10
    (op_delegatecall_prefix2_r32 hW
      (handlerRunA_of_childContinuation_g10 s0 _ _ (dcRest_ccA_r32 hW hgc32)))

/-! ## `op_staticcall` under the child-push contract -/

theorem extCodeChain_ccA_r32 {F : Type} (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    @ChildContinuationA F scXQ extCodeProg_g10 := by
  apply ccA_decCall_g10 (Q := scXQ) hW.epsA_ext_code_of
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hgk, _, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
    exact hm32
  apply ccA_decCall_g10 (Q := scXQ) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_decCall_g10 (Q := scXQ) epsA_calculate_message_call_gas
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
    (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
    obtain ⟨hglob, hm32⟩ := hQc
    refine scXQ_of_pins_g10 hp ?_
    rw [globN_congr_g10 hglob "ev"]
    exact hm32
  apply ccA_seq_store_ev_g10 (Q := scXQ) 184 (by decide)
    (hval := fun t v _ hv => eval_op_word_g10 _ _ v hv)
    (hstep := fun t w _ hi _ hp => scXQ_of_updW_g10 184 (by decide) (by decide) hi w hp)
  apply ccA_seq_call_g10 (Q := XShQ_g10) epsA_extend_memory
    (hentry := fun t values body callee rs hc hi hw hp ha hl =>
      memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl)
    (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
      obtain ⟨cw, ebw, hxl, _⟩ := hp
      exact ⟨cw, ebw, hxl⟩)
  apply ccA_dec_g10 (Q := XShQ_g10)
    (hinit := fun t v _ _ hp => xShQ_setvar_g10 (by decide) hp)
  apply ccA_seq_store_ev_g10 (Q := XShQ_g10) 72 (by decide)
    (hval := fun t v _ hv => ⟨(BitVec.ofNat 64 0), eval_const_word_g10 _ v hv⟩)
    (hstep := fun t w _ _ _ hp => xShQ_of_updW_g10 72 w hp)
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_g10 (Q := XShQ_g10) epsA_sat_word
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact xShQ_setvar_g10 (by decide) hp
  apply ccA_decCall_childCall_r32 hgc32
    (hnoraise := fun t' w hl hw => by exact noEvmErr_afterCall_r32 t' w hl hw)
  apply ccA_seq_ite_g10
  · intro t w hcond hw0
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add
      (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial)
      (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
      (ccA_ret_g10 (.const 0#64))
  · intro t hcond
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const 0#64))

theorem dlChain_ccA_r32 {F : Type} (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    @ChildContinuationA F scXQ
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
        (ofString "calculate_delegation_cost") [.var .local (ofString "to")]
        (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
          (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
              (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.rfield 2 (.var .local (ofString "dl"))])
              (.call (some (none, none)) (ofString "warm_address")
                [.var .local (ofString "code_address")]))
            .skip)
            extCodeProg_g10))) := by
  apply ccA_decCall_g10 (Q := scXQ) (epsA_cdc_full_g10 hW)
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    obtain ⟨hpins, _, _⟩ := hQc
    obtain ⟨hev, hm32, _⟩ := hpins v rfl
    refine scXQ_setvar_g10 (by decide) (scXQ_of_pins_g10 hp ?_)
    rw [hev]
    exact hm32
  apply ccA_dec_g10 (Q := scXQ)
    (hinit := fun t v _ _ hp => scXQ_setvar_g10 (by decide) hp)
  apply ccA_seq_ite_g10
  · intro t w _ _
    rw [ccA_seq_seq_assoc_g10]
    apply ccA_seq_call_g10 (Q := scXQ) epsA_charge_gas_keep32
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
    · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
      obtain ⟨hglob, hm32⟩ := hQc
      refine scXQ_of_pins_g10 hp ?_
      rw [globN_congr_g10 hglob "ev"]
      exact hm32
    · apply ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
        (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      · intro t values body callee rs v cpost _ _ hp _ _ _ hQc
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32
      · exact extCodeChain_ccA_r32 hW hgc32
  · intro t _
    exact ccA_seq_skip_g10 (extCodeChain_ccA_r32 hW hgc32)

/-! ### The `op_staticcall` rest (nodes 18-47) -/

theorem staticcallRest_ccA_r32 {F : Type} (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    @ChildContinuationA F scXQ
      (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address") [.var .local (ofString "to")])
          .skip)
        (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost") [.var .local (ofString "to")]
          (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
            (.seq (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
                (.const (BitVec.ofNat 64 0)))
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                  [.rfield 2 (.var .local (ofString "dl"))])
                (.call (some (none, none)) (ofString "warm_address")
                  [.var .local (ofString "code_address")]))
              .skip)
              extCodeProg_g10)))) := by
  apply ccA_seq_ite_g10
  · intro t w _ _
    exact ccA_seq_call_g10 (Q := scXQ) Group10.epsA_warm_address_keep32_g10
      (hentry := fun t values body callee rs _ _ _ _ _ _ => trivial)
      (hstep := fun t values body callee rs v cpost _ _ hp _ _ _ hQc => by
        obtain ⟨hgk, _, hm32⟩ := hQc
        refine scXQ_of_pins_g10 hp ?_
        rw [globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm]
        exact hm32)
      (dlChain_ccA_r32 hW hgc32)
  · intro t _
    exact ccA_seq_skip_g10 (dlChain_ccA_r32 hW hgc32)

/-! ### The `op_staticcall` need chain (nodes 14-16) -/

theorem op_staticcall_needChain_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 (fun s => scXQ s ∧ AcQ_g10 s) charged
      (.decCall (ofString "need") .one (ofString "add_sat")
        [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
        (.seq (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "need")])
          cont)) := by
  apply HandlerRunA.decCall (Q := fun s => scXQ s ∧ NdQ_g10 s) epsA_add_sat_ge_g10
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost hi hw hp hargs hlk hi2 hw2 hch hQc
    obtain ⟨hlf, aw, rw, hla, hvw, hle⟩ := hQc
    obtain ⟨acw, hl_ac, hac⟩ := hp.2
    obtain ⟨v0, v1, hv0_ev, hv1_ev, hvals⟩ : ∃ v0 v1,
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) = some v0 ∧
        @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) = some v1 ∧
        values = [v0, v1] := by
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      rcases he0 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "access_cost")) with _ | v0
      · simp [he0] at hargs
      rcases he1 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | v1
      · simp [he0, he1] at hargs
      simp only [he0, he1, Option.some.injEq] at hargs
      exact ⟨v0, v1, rfl, rfl, hargs.symm⟩
    subst hvals
    obtain ⟨w0, w1, hv0w, hv1w, hla0, _⟩ := add_sat_args_lookup_g10 hlk
    have hv0_acw : t.locals.lookup (ofString "access_cost") = some (.val (.word w0)) := by
      rw [← hv0w]; exact hv0_ev
    have hw0_acw : w0 = acw := by
      have h := hl_ac.symm.trans hv0_acw
      injection h with h1
      injection h1 with h2
      injection h2 with h3
      exact h3.symm
    have hla' : callee.lookup (ofString "a") = some (.val (.word aw)) := hla
    have haw : aw = w0 := by
      have h := hla'.symm.trans hla0
      injection h with h1
      injection h1 with h2
      injection h2 with h3
    have hle_nat : aw.toNat ≤ rw.toNat := hle
    rw [haw, hw0_acw] at hle_nat
    have h100 : 100 ≤ acw.toNat := by rcases hac with rfl | rfl <;> simp
    refine ⟨scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp.1 hlf), rw, ?_, ?_⟩
    · dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl, hvw] | simp [hvw]
    · omega
  apply HandlerRunA.seq_charge_gas_keep32_g10 (Q := scXQ)
    (hpos := fun t w hv _ _ hp => by
      obtain ⟨nw, hlk_n, hbound⟩ := hp.2
      have hev : t.locals.lookup (ofString "need") = some (.val (.word w)) := hv
      rw [hlk_n] at hev
      injection hev with h1
      injection h1 with h2
      injection h2 with h3
      subst h3
      omega)
    (hstep := fun t cpost _ _ hp _ _ _ hm32 _ => scXQ_of_pins_g10 hp.1 hm32)
    (hcont := hcont)

/-! ### The `op_staticcall` compiled prefix (nodes 10-16) -/

theorem op_staticcall_prefix2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {cont : ProgHOL 64} (hW : WorldAccountSpecsA)
    (hcont : HandlerRunA s0 scXQ true cont) :
    HandlerRunA s0 scXQ charged
      (.decCall (ofString "warm") .one (ofString "is_warm_address") [.var .local (ofString "to")]
        (.dec (ofString "access_cost") .one (.const (BitVec.ofNat 64 100))
          (.seq (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
              (.assign .local (ofString "access_cost") (.const (BitVec.ofNat 64 3000))) .skip)
            (.decCall (ofString "need") .one (ofString "add_sat")
              [.var .local (ofString "access_cost"), .rfield 0 (.var .local (ofString "x"))]
              (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.var .local (ofString "need")]) cont))))) := by
  apply HandlerRunA.decCall (Q := scXQ) epsA_is_warm_address
    (hentry := fun t values body' callee ret' _ _ _ _ _ _ => trivial)
  · intro t values body callee rs v cpost _ _ hp _ _ _ _ _ hQc
    exact scXQ_setvar_g10 (by decide) (scXQ_of_locFrame_call_g10 hp hQc)
  apply HandlerRunA.dec (Q := fun s => scXQ s ∧ AcQ_g10 s)
    (hinit := fun t v hv _ hp => by
      have hvw : v = .val (.word (BitVec.ofNat 64 100)) := eval_const_word_g10 _ v hv
      subst hvw
      refine ⟨scXQ_setvar_g10 (by decide) hp, (BitVec.ofNat 64 100), ?_, Or.inl rfl⟩
      dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      first | rw [if_pos rfl] | simp)
  apply HandlerRunA.seq_ite_unit
  · intro t w _ _
    apply HandlerRunA.seq_assign_local (Q := fun s => scXQ s ∧ AcQ_g10 s)
      (hasgn := fun t v hv _ hp => by
        have hvw : v = .val (.word (BitVec.ofNat 64 3000)) := eval_const_word_g10 _ v hv
        subst hvw
        refine ⟨scXQ_setvar_g10 (by decide) hp.1, (BitVec.ofNat 64 3000), ?_, Or.inr rfl⟩
        dsimp only [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
        first | rw [if_pos rfl] | simp)
    exact op_staticcall_needChain_r32 hW hcont
  · intro t _
    exact HandlerRunA.seq_skip (op_staticcall_needChain_r32 hW hcont)

/-! ### `op_staticcall` assembly -/

theorem op_staticcall_run_full_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hW : WorldAccountSpecsA) (hgc32 : callSpec_generic_call_r32) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_staticcall) :=
  op_staticcall_prefix1_g10
    (op_staticcall_prefix2_r32 hW
      (handlerRunA_of_childContinuation_g10 s0 _ _ (staticcallRest_ccA_r32 hW hgc32)))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
