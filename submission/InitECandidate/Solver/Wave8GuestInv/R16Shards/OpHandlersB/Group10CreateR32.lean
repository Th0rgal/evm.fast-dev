import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreates
import InitECandidate.Solver.Wave8GuestInv.ContractParts.WitnessDbStorageR31

/-! # R32: op_create / op_create2 handler specs with a child-push `generic_create` callee

`generic_create` pushes a child frame (via `start_child`) when creation proceeds, so it is
NOT an `EvmPreservingSpecA` callee (the chain grows on its return). This file introduces
`ChildCreateSpecA`, the child-push analogue: the callee returns `0` with the chain unchanged,
or returns a nonzero word having pushed exactly one frame (the new head being the callee's
exit state's own head); its own `EvmErr` exits keep the chain depth.

Part 1 (`createSpec_generic_create_r32`) assembles that spec from body-level push facts:
`HeadMemChainWF post` is derived (not assumed) via `Group10.headMemChainWF_push` /
`headMemChainWF_of_locFrame`.

Part 2 re-drives the already-compiled op_create / op_create2 prefixes: the charged suffix
tails are re-proven with the unconditional `epsA_get_account_r31` (replacing the
`WorldAccountSpecsA` witness) and `ccA_decCall_childCreate_r32` (the child-push analogue of
`ccA_decCall_g10`). Because `generic_create`'s only nonzero-return path pushes a frame and
the opcodes' tail after it is `ite (started = 0) (pc_add 1) skip; return 0` — which cannot
raise `EvmErr` once `started ≠ 0` — the error-depth obligation of `ChildContinuationA` is
discharged by `noEvmErr_afterCreate_r32`. -/

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

/-! ## 1. The child-push callee spec -/

/-- Child-push callee spec for `generic_create`: the shape of `EvmPreservingSpecA`, except
the return case allows the chain to grow by exactly the callee's exit-state head (when it
returns a nonzero word), while returning `0` keeps the chain; `EvmErr` exits keep the depth. -/
def ChildCreateSpecA
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Qret : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      EvmInv s → Group10.HeadMemChainWF s → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      let r := (evaluateHOLFiniteState s body).1
      let post := (evaluateHOLFiniteState s body).2
      (∀ v, r = some (.returned v) →
        ((v = .val (.word 0#64) ∧ evmChain post = evmChain s) ∨
          (∃ w : BitVec 64, w ≠ 0 ∧ v = .val (.word w) ∧
            evmChain post = (globN post "ev", globN post "cur_cont") :: evmChain s)) ∧
        EvmInv post ∧ Group10.HeadMemChainWF post ∧ evmR post ≤ evmR s ∧ Qret s v post) ∧
      (IsEvmErr r → (EvmInv post ∧ Group10.HeadMemChainWF post) ∧
        (evmChain post).length = (evmChain s).length ∧ evmR post ≤ evmR s)

theorem lookup_generic_create_r32 :
    originalRuntimeCode.lookup (ofString "generic_create") =
      some ([(ofString "endowment", .comb [.one, .one, .one, .one]),
        (ofString "contract_address", .one), (ofString "mstart", .one), (ofString "msize", .one)],
        sourceFnBody Guest.Software.guestFn_generic_create, .one) :=
  lookup_of_guestAst_getElem 598 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_generic_create) rfl

/-- The `generic_create` callee spec, assembled from body-level outcome facts. The push
branch's hypotheses are exactly the frame-local facts delivered by the `start_child`
machinery (new-head alignment, `mem + cap = frame_mem_ptr`, the child continuation's mark
equalling the old `frame_mem_ptr`, and cell agreement for the old frames); the theorem
derives `HeadMemChainWF post` itself via `Group10.headMemChainWF_push`, and `LocFrame`
keeps the invariant on the chain-unchanged branches. -/
theorem createSpec_generic_create_r32
    (hbody : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      EvmInv s → Group10.HeadMemChainWF s →
      let r := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_generic_create)).1
      let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_generic_create)).2
      r ≠ some .timeOut →
      ((∀ v, r = some (.returned v) →
          ((v = .val (.word 0#64) ∧ evmChain post = evmChain s) ∨
            (∃ w : BitVec 64, w ≠ 0 ∧ v = .val (.word w) ∧
              evmChain post = (globN post "ev", globN post "cur_cont") :: evmChain s ∧
              memW post (globN post "ev" + 32) % 32 = 0 ∧
              memW post (globN post "ev" + 40) % 8 = 0 ∧
              memW post (globN post "ev" + 24) + memW post (globN post "ev" + 40) =
                globN post "frame_mem_ptr" ∧
              memW post (globN post "cur_cont" + 56) = globN s "frame_mem_ptr" ∧
              ∀ ec ∈ evmChain s,
                memW post (ec.1 + 24) = memW s (ec.1 + 24) ∧
                memW post (ec.1 + 32) = memW s (ec.1 + 32) ∧
                memW post (ec.1 + 40) = memW s (ec.1 + 40) ∧
                memW post (ec.2 + 56) = memW s (ec.2 + 56))) ∧
        EvmInv post ∧ LocFrame s post ∧ evmR post ≤ evmR s) ∧
      (IsEvmErr r → evmChain post = evmChain s ∧ EvmInv post ∧ LocFrame s post ∧
        evmR post ≤ evmR s))) :
    ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create") := by
  refine ⟨_, sourceFnBody Guest.Software.guestFn_generic_create, _,
    lookup_generic_create_r32, ?_⟩
  intro F s hcode hinv hwf _ _ hnt
  obtain ⟨r, hr⟩ : ∃ r, (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_generic_create)).1 = r := ⟨_, rfl⟩
  rw [hr] at ⊢
  obtain ⟨post, hp⟩ : ∃ post, (evaluateHOLFiniteState s
      (sourceFnBody Guest.Software.guestFn_generic_create)).2 = post := ⟨_, rfl⟩
  rw [hp] at ⊢
  have hb := hbody s hcode hinv hwf hnt
  rw [hr, hp] at hb
  obtain ⟨hret, herr⟩ := hb
  refine ⟨fun v hv => ?_, fun he => ?_⟩
  · obtain ⟨hcase, hi, hlf, hR⟩ := hret v hv
    have hwf' : Group10.HeadMemChainWF post := by
      rcases hcase with ⟨hz0, -⟩ | ⟨w, hw0, hvw, hch, hlen, hcap, hend, hmark, hmem⟩
      · exact headMemChainWF_of_locFrame hwf hlf
      · exact Group10.headMemChainWF_push hwf hch hmem hlen hcap hend hmark
    refine ⟨?_, hi, hwf', hR, hlf⟩
    rcases hcase with ⟨hz0, hch0⟩ | ⟨w, hw0, hvw, hch, hlen, hcap, hend, hmark, hmem⟩
    · exact Or.inl ⟨hz0, hch0⟩
    · exact Or.inr ⟨w, hw0, hvw, hch⟩
  · obtain ⟨hch, hi, hlf, hR⟩ := herr he
    exact ⟨⟨hi, headMemChainWF_of_locFrame hwf hlf⟩, by rw [hch], hR⟩

/-! ## 2. The child-push decCall step -/

/-- After `generic_create` returns a nonzero word (the push case), the opcodes' tail
`ite (started = 0) (pc_add 1) skip; return 0` cannot produce `EvmErr`: the condition
evaluates false, so the tail is `skip; return 0`. -/
theorem noEvmErr_afterCreate_r32 {F : Type} (t' : PanSemStateFiniteExact 64 F)
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

/-- `ccA_decCall_g10` for a child-push callee: on the callee's own `EvmErr` its depth is
kept (the spec's error case), and after a nonzero return the continuation cannot raise
(`hnoraise`), so `ChildContinuationA`'s error-depth obligation holds; the return case needs
no chain condition at all. -/
theorem ccA_decCall_childCreate_r32 {F : Type} {P : PanSemStateFiniteExact 64 F → Prop}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post) fname)
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
              ((v = .val (.word 0#64) ∧
                  evmChain cpost = evmChain (callEntryStateHOLFinite t callee)) ∨
                (∃ w : BitVec 64, w ≠ 0 ∧ v = .val (.word w) ∧
                  evmChain cpost = (globN cpost "ev", globN cpost "cur_cont") ::
                    evmChain (callEntryStateHOLFinite t callee))) ∧
              EvmInv cpost ∧ Group10.HeadMemChainWF cpost ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              LocFrame (callEntryStateHOLFinite t callee) cpost) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
              (evmChain cpost).length = (evmChain (callEntryStateHOLFinite t callee)).length ∧
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
              obtain ⟨hcase, hi_cp, hw_cp, hR_cp, -⟩ := (hQ (by simp)).1 v rfl
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
                rcases hcase with ⟨-, hch_cp⟩ | ⟨w, hw0, hvw, hpush⟩
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
              obtain ⟨⟨hi_cp, hw_cp⟩, hlen_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := R11Shards.OpDispatchSpec.evm_congr (s := cpost)
                (t := (cpost.emptyLocalsHOLFinite : PanSemStateFiniteExact 64 F)) rfl rfl
              refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h), fun _ => ?_⟩
              exact ⟨⟨hi_el, hw_el⟩, by rw [hc_el.2.2.1, hlen_cp, hc_ce.2.2.1],
                by rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp⟩
            · refine ⟨fun hr => absurd hr (by rintro ⟨_, h⟩; cases h),
                fun he => absurd he ?_⟩
              intro hc
              obtain ⟨_, hv⟩ := hc
              injection hv with h'; injection h' with h1 _
              exact heid h1
          | «break» | «continue» | error | finalFfi _ =>
            refine ⟨fun hv => absurd hv (by rintro ⟨_, h⟩; cases h),
              fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩

/-! ## 3. op_create suffix tail walk and spec -/

theorem createChargedSuffixTail_ccA_r32 {F : Type}
    (hcc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_contract_address"))
    (hgc : ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create")) :
    ChildContinuationA (F := F) (fun _ => True) (handlerSuffix_g10 1 createChargedSuffix_g10) := by
  apply ccA_dec_g10 (Q := fun _ => True) (fun t v hv hi hp => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) ContractParts.epsA_get_account_r31
    (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) epsA_alloc_g10
    (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ _ _ => trivial)
  apply ccA_seq_call_g10 (Q := fun _ => True) hcc
    (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word
    (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_childCreate_r32 hgc
    (hnoraise := fun t' w hl hw => by exact noEvmErr_afterCreate_r32 t' w hl hw)
  apply ccA_seq_ite_g10
  · intro t w hcond hw0
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add
      (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial)
      (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
      (ccA_ret_g10 (.const 0#64))
  · intro t hcond
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const 0#64))

theorem op_create_run_full_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hcc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_contract_address"))
    (hgc : ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create")) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create) :=
  create_prefix_through_extend_g10 s0
    (handlerRunA_of_childContinuation_g10 s0 _ _ (createChargedSuffixTail_ccA_r32 hcc hgc))

theorem op_create_specA_r32 (hcc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_contract_address"))
    (hgc : ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create")) :
    OpHandlerSpecA (ofString "op_create") := by
  refine opHandlerSpecA_of_run 599 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_create rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact op_create_run_full_r32 s0 hcc hgc

/-! ## 4. op_create2 suffix tail walk and spec -/

theorem create2ChargedSuffixTail_ccA_r32 {F : Type}
    (hU : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc2 : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgc : ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create")) :
    ChildContinuationA (F := F) MemoryExpansionLocal_g10
      (handlerSuffix_g10 1 create2ChargedSuffix_g10) := by
  apply ccA_seq_call_g10 (Q := MemoryExpansionLocal_g10) hU
    (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost hi hw hp hci hw2 hch hq => by
      unfold LocFrame at hq
      have hgg := congrArg PanSemStateFiniteExact.globals hq
      have hmm := congrArg PanSemStateFiniteExact.memory hq
      refine memoryExpansionLocal_transport_g10 hp ?_ ?_ ?_
      · rfl
      · show globN { cpost with locals := t.locals } "ev" = globN t "ev"
        unfold globN
        rw [hgg]
        rfl
      · show memW { cpost with locals := t.locals } _ = memW t _
        unfold memW
        rw [hmm]
        rfl)
  apply ccA_seq_call_g10 (Q := fun _ => True) epsA_extend_memory
    (hentry := fun t values body callee rs hc hi hw hp ha hl =>
      memoryExpansionLocal_callee_pre_g10 t hc hw hp ha hl)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
  apply ccA_dec_g10 (Q := fun _ => True) (fun t v hv hi hp => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) epsA_sat_word
    (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_g10 (Q := fun _ => True) epsA_alloc_g10
    (hentry := fun t values body callee ret' hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ _ _ => trivial)
  apply ccA_seq_call_g10 (Q := fun _ => True) hcc2
    (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial)
    (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
  apply ccA_decCall_childCreate_r32 hgc
    (hnoraise := fun t' w hl hw => by exact noEvmErr_afterCreate_r32 t' w hl hw)
  apply ccA_seq_ite_g10
  · intro t w hcond hw0
    exact ccA_seq_call_g10 (Q := fun _ => True) epsA_pc_add
      (hentry := fun t values body callee rs hc hi hw hp ha hl => trivial)
      (hstep := fun t values body callee rs v cpost _ _ _ _ _ _ _ => trivial)
      (ccA_ret_g10 (.const 0#64))
  · intro t hcond
    exact ccA_seq_skip_g10 (ccA_ret_g10 (.const 0#64))

theorem op_create2_run_full_r32 {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (hU : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc2 : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgc : ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create")) :
    HandlerRunA s0 (fun _ => True) false (sourceFnBody Guest.Software.guestFn_op_create2) :=
  create2_prefix_through_alloc_g10 s0
    (handlerRunA_of_childContinuation_g10 s0 _ _ (create2ChargedSuffixTail_ccA_r32 hU hcc2 hgc))

theorem op_create2_specA_r32 (hU : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc2 : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgc : ChildCreateSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create")) :
    OpHandlerSpecA (ofString "op_create2") := by
  refine opHandlerSpecA_of_run 600 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_create2 rfl ?_
  intro F s0 hInv0 hWF0 hnd0
  exact op_create2_run_full_r32 s0 hU hcc2 hgc

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
