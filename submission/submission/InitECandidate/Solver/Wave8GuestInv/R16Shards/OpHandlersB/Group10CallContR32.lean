import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallGenR32

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

local notation "evmR" => R16Shards.evmR

/-! #R#32 slot 6c: the four call specs closed under the child-push
`generic_call` contract.  This module rebuilds the compiled `op_call` and
`op_callcode` tail walks with `callSpec_generic_call_r32` replacing the old
chain-preserving assumption, inhabits `Group10CallR32Continuations`, and
discharges the four `*_specA_r32` theorems unconditionally over
`WorldAccountSpecsCall_g10R32`. -/

/-! ## Local copies of private bound-transfer helpers -/

private theorem rboundA_step_r32 {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem rboundA_to_le_r32 {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h ⊢ <;> omega

/-! ## The `started == 0` test under a local binding -/

/-- If the local `nm` holds the word `w`, the `started == 0` test `nm == 0`
evaluates to word `1` exactly when `w` is zero and to word `0` otherwise. -/
theorem cmp_eq_var_zero_r32c {F : Type} {t : PanSemStateFiniteExact 64 F} {nm : MlS}
    {w : BitVec 64}
    (hlk : t.locals.lookup nm = some (.val (.word w))) :
    @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.cmp .equal (.var .local nm) (.const (BitVec.ofNat 64 0))) =
      some (.val (.word (if w = 0#64 then 1#64 else 0#64))) := by
  simp [evalHOLExact, hlk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

/-! ## The child-push bound-call combinator -/

/-- The `HandlerRunA` analogue of `HandlerRunA.seq_call_assign_local` for a
child-pushing callee: on a normal return with result word `0` the continuation
`callcodeContProg_g10` runs on the assigned state as before, while a pushed
child frame (nonzero result word) makes the `started == 0` test fail and the
suffix collapse to `skip; return 0` on emptied locals, with the strict
potential drop supplied by `hpushR` (the caller's credit invariant).  Shape
mismatches and invalid assignments fault to `.error`, which is neither a
normal return nor `IsEvmErr`, so both `OpDispatchPostA` obligations close
trivially there. -/
theorem HandlerRunA.seq_call_childCall_r32
    {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {args : List (ExpHOL 64)}
    (hf : EvmChildPushSpecA (fun _ => True) (fun s _ post => LocFrame s post) fname)
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) values body callee retShape v
        (cpost : PanSemStateFiniteExact 64 F),
      EvmInv t → Group10.HeadMemChainWF t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      shapeEqHOL (shapeOfHOLExact v) retShape = true →
      EvmInv cpost → Group10.HeadMemChainWF cpost →
      evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      LocFrame (callEntryStateHOLFinite t callee) cpost →
      Q (setVarHOLFinite (ofString "started") v { cpost with locals := t.locals }))
    (hpushR : ∀ (t : PanSemStateFiniteExact 64 F), P t →
      R11Shards.OpDispatchSpec.evmR t < R11Shards.OpDispatchSpec.evmR s0)
    (hcont : HandlerRunA s0 Q charged callcodeContProg_g10) :
    HandlerRunA s0 P charged
      (.seq (.call (some (some (.local, (ofString "started")), none)) fname args) callcodeContProg_g10) := by
  intro t hc hi hw hlen hR hp hn
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hn ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · dsimp only; exact opDispatchPostA_error s0 t
  · simp only [hargs] at hn ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · dsimp only; exact opDispatchPostA_error s0 t
    · simp only [hl] at hn ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hn
      · simp only [hz, ↓reduceIte] at hn ⊢
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
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hw_ce : Group10.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          Group10.headMemChainWF_locals t callee (t.clock - 1) hw
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hn hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := R11Shards.OpDispatchSpec.evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
                R11Shards.OpDispatchSpec.evmR cpost ≤
                R11Shards.OpDispatchSpec.evmR (callEntryStateHOLFinite t callee) ∧
                LocFrame (callEntryStateHOLFinite t callee) cpost ∧
                ((v = .val (.word 0#64) ∧
                    evmChain cpost = evmChain (callEntryStateHOLFinite t callee)) ∨
                  ((evmChain cpost).length =
                      (evmChain (callEntryStateHOLFinite t callee)).length + 1 ∧
                    ∃ w : BitVec 64, w ≠ 0#64 ∧ v = .val (.word w)))) ∧
            (IsEvmErr res →
              (EvmInv cpost ∧ Group10.HeadMemChainWF cpost) ∧
                evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
                R11Shards.OpDispatchSpec.evmR cpost ≤
                R11Shards.OpDispatchSpec.evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hi_ce hw_ce trivial
            ⟨values, hl_orig⟩ (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => dsimp only; exact opDispatchPostA_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hn
          | returned v =>
            dsimp only at hn ⊢
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hn ⊢
              by_cases hvld : isValidValueHOLExact t.toExact .local (ofString "started") v = true
              · simp only [hvld, ↓reduceIte] at hn ⊢
                dsimp only [setKvarHOLFinite] at hn ⊢
                obtain ⟨⟨hi_cp, hw_cp⟩, hR_cp, hQc_cp, hcorr⟩ := (hQ (by simp)).1 v rfl
                have hcode_res : (setVarHOLFinite (ofString "started") v { cpost with locals := t.locals }).code =
                    originalRuntimeCode := hmeta.trans hc
                have hi_res : EvmInv (setVarHOLFinite (ofString "started") v { cpost with locals := t.locals }) :=
                  localsFree_evmInv cpost _ cpost.clock hi_cp
                have hw_res : Group10.HeadMemChainWF
                    (setVarHOLFinite (ofString "started") v { cpost with locals := t.locals }) :=
                  Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
                have hc_res := R11Shards.OpDispatchSpec.evm_congr (s := cpost)
                  (t := (setVarHOLFinite (ofString "started") v { cpost with locals := t.locals } :
                    PanSemStateFiniteExact 64 F)) rfl rfl
                rcases hcorr with ⟨hv0, hch_cp⟩ | ⟨-, w, hw0, hvw⟩
                · -- no child pushed: the continuation runs on the assigned state
                  subst hv0
                  have hlen_res : (evmChain (setVarHOLFinite (ofString "started") (.val (.word 0#64))
                      { cpost with locals := t.locals })).length = (evmChain s0).length := by
                    rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
                  have hR_res : if charged then R11Shards.OpDispatchSpec.evmR
                        (setVarHOLFinite (ofString "started") (.val (.word 0#64)) { cpost with locals := t.locals }) <
                      R11Shards.OpDispatchSpec.evmR s0
                      else R11Shards.OpDispatchSpec.evmR
                        (setVarHOLFinite (ofString "started") (.val (.word 0#64)) { cpost with locals := t.locals }) ≤
                      R11Shards.OpDispatchSpec.evmR s0 :=
                    rboundA_step_r32 (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
                  have hQ_res : Q (setVarHOLFinite (ofString "started") (.val (.word 0#64))
                      { cpost with locals := t.locals }) :=
                    hstep t values body callee retShape (.val (.word 0#64)) cpost hi hw hp
                      hargs hl_orig hsh_ok hi_cp hw_cp hch_cp hQc_cp
                  exact hcont _ hcode_res hi_res hw_res hlen_res hR_res hQ_res hn
                · -- child pushed: `started` is the nonzero word `w`, so the
                  -- `started == 0` test evaluates to word `0` and the suffix
                  -- collapses to `skip; return 0`
                  subst hvw
                  have hlk1 : (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals }).locals.lookup (ofString "started")
                      = some (.val (.word w)) := by
                    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                  have hcond : @evalHOLExact 64 F _
                      (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals }).toExact
                      (fun a => Classical.propDecidable
                        ((setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals }).memaddrs a))
                      (.cmp .equal (.var .local (ofString "started")) (.const (BitVec.ofNat 64 0))) =
                      some (.val (.word (if w = 0#64 then 1#64 else 0#64))) :=
                    cmp_eq_var_zero_r32c hlk1
                  rw [if_neg hw0] at hcond
                  have hconst : @evalHOLExact 64 F _
                      (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals }).toExact
                      (fun a => Classical.propDecidable
                        ((setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals }).memaddrs a))
                      (.const (BitVec.ofNat 64 0)) =
                      some (.val (.word (BitVec.ofNat 64 0))) := by
                    simp only [evalHOLExact]
                  have hsz : sizeOfShapeWithContextHOL
                      (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals }).structs
                      (shapeOfHOLExact (.val (.word (BitVec.ofNat 64 0)) : ValueHOL 64)) ≤ 32 := by
                    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                  have hres : evaluateHOLFiniteState
                      (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals })
                      callcodeContProg_g10 =
                      (some (.returned (.val (.word (BitVec.ofNat 64 0)))),
                        emptyLocalsHOLFinite
                          (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals })) := by
                    simp only [callcodeContProg_g10]
                    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, hcond]
                    simp only [↓reduceIte, evaluateHOLFiniteState_skip]
                    rw [if_pos (by decide : (0#64 : BitVec 64) = 0)]
                    rw [evaluateHOLFiniteState_return]
                    dsimp only
                    rw [hconst]
                    dsimp only
                    rw [if_pos hsz]
                  rw [hres] at hn ⊢
                  dsimp only at hn ⊢
                  have hi_el : EvmInv (emptyLocalsHOLFinite
                      (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals })) :=
                    localsFree_evmInv _ _ _ hi_res
                  have hw_el : Group10.HeadMemChainWF (emptyLocalsHOLFinite
                      (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals })) :=
                    Group10.headMemChainWF_locals _ _ _ hw_res
                  have hc_el := R11Shards.OpDispatchSpec.evm_congr
                    (s := (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals } :
                      PanSemStateFiniteExact 64 F))
                    (t := (emptyLocalsHOLFinite
                      (setVarHOLFinite (ofString "started") (.val (.word w)) { cpost with locals := t.locals }) :
                      PanSemStateFiniteExact 64 F)) rfl rfl
                  rw [hc_ce.2.1] at hR_cp
                  refine ⟨fun _ => ⟨⟨hi_el, hw_el⟩, evmPot_lt_of_evmR_lt hi_el ?_⟩,
                    fun he => absurd he (by rintro ⟨_, h⟩; cases h)⟩
                  rw [hc_el.2.1, hc_res.2.1]
                  exact lt_of_le_of_lt hR_cp (hpushR t hp)
              · simp only [hvld, Bool.false_eq_true, ↓reduceIte]
                exact opDispatchPostA_error s0 cpost
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostA_error s0 cpost
          | exception eid ev =>
            dsimp only at hn ⊢
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨⟨hi_cp, hw_cp⟩, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hw_el : Group10.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group10.headMemChainWF_locals cpost _ cpost.clock hw_cp
              have hc_el := R11Shards.OpDispatchSpec.evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨⟨hi_el, hw_el⟩, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rboundA_to_le_r32 hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPostA_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => dsimp only; exact opDispatchPostA_error s0 cpost
          | «continue» => dsimp only; exact opDispatchPostA_error s0 cpost
          | finalFfi _ =>
            dsimp only
            refine opDispatchPostA_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => dsimp only; exact opDispatchPostA_error s0 cpost.emptyLocalsHOLFinite

/-! ## `op_callcode` under the child-push contract -/
theorem callcodeGenericCall2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc32 : callSpec_generic_call_r32)
 :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq
        (.call (some (some (.local, ofString "started"), none)) (ofString "generic_call")
          [.rfield 1 (.var .local (ofString "mcg")),
           .var .local (ofString "reservoir"),
           .var .local (ofString "value"),
           .var .local (ofString "to"),
           .var .local (ofString "to"),
           .var .local (ofString "code_address"),
            .const (BitVec.ofNat 64 1),
            .const (BitVec.ofNat 64 0),
            .var .local (ofString "is"),
            .var .local (ofString "isz"),
            .var .local (ofString "os"),
            .var .local (ofString "osz"),
            .rfield 0 (.var .local (ofString "code")),
           .rfield 1 (.var .local (ofString "code")),
           .rfield 0 (.var .local (ofString "dl")),
           .const (BitVec.ofNat 64 0)])
        callcodeContProg_g10) :=
  HandlerRunA.seq_call_childCall_r32 hgc32
    (fun t values body callee retShape v cpost hi hw hp hargs hl hshp hi_cp hw_cp hch_cp hQc =>
      CcR2Q_setVarRes_g10 (by decide)
        (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp)
    (fun t ht => by
      obtain ⟨w0, w1, hmcg, hcredit, -⟩ := ht
      have h' : R11Shards.OpDispatchSpec.evmR t + w1.toNat + 1 ≤
          R11Shards.OpDispatchSpec.evmR s0 := hcredit
      omega)
    (HandlerRunA.weaken (fun t ht hp => trivial) callcodeCont_run_g10)
theorem callcodeStarted2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.dec (ofString "started") .one (.const (BitVec.ofNat 64 0)) cont) :=
  HandlerRunA.dec_carry_g10 (fun t v hp => CcR2Q_setVar_g10 (by decide) hp)
    hcont

theorem callcodeInsufficient2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.decCall (ofString "insufficient") .one (ofString "u256_lt")
        [.load (.comb [.one, .one, .one, .one])
           (.op .add [.var .local (ofString "sender"), .const (BitVec.ofNat 64 8)]),
         .var .local (ofString "value")]
        cont) := by
  refine HandlerRunA.decCall epsA_u256_lt (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    exact CcR2Q_setVarRes_g10 (by decide)
      (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp

theorem callcodeSender2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.decCall (ofString "sender") .one (ofString "get_account")
        [.var .local (ofString "to")] cont) := by
  refine HandlerRunA.decCall hW.epsA_get_account (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hgk, hRev⟩ := hQc
    exact CcR2Q_setVarRes_g10 (by decide) (le_of_eq (hRev.trans evmR_entry_eq_g10)) hp

theorem callcodeInsfTail2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc32 : callSpec_generic_call_r32)
 :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "insufficient"))
            (.const (BitVec.ofNat 64 0)))
          (.seq (.call (some (none, none)) (ofString "stack_push")
              [.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)]])
            (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
              (.seq (.call (some (none, none)) (ofString "set_retdata")
                  [.var .local (ofString "empty"), .const (BitVec.ofNat 64 0)])
                (.seq (.store (.op .add [.var .global (ofString "ev"),
                      .const (BitVec.ofNat 64 64)])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"),
                         .const (BitVec.ofNat 64 64)]),
                       .rfield 1 (.var .local (ofString "mcg"))]))
                  (.store (.op .add [.var .global (ofString "ev"),
                      .const (BitVec.ofNat 64 72)])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"),
                         .const (BitVec.ofNat 64 72)]),
                       .var .local (ofString "reservoir")]))))))
          (.decCall (ofString "is") .one (ofString "sat_word")
            [.var .local (ofString "in_start")]
            (.decCall (ofString "isz") .one (ofString "sat_word")
              [.var .local (ofString "in_size")]
              (.decCall (ofString "os") .one (ofString "sat_word")
                [.var .local (ofString "out_start")]
                (.decCall (ofString "osz") .one (ofString "sat_word")
                  [.var .local (ofString "out_size")]
                  (.call (some (some (.local, ofString "started"), none))
                    (ofString "generic_call")
                    [.rfield 1 (.var .local (ofString "mcg")),
                     .var .local (ofString "reservoir"),
                     .var .local (ofString "value"),
                     .var .local (ofString "to"),
                     .var .local (ofString "to"),
                     .var .local (ofString "code_address"),
                     .const (BitVec.ofNat 64 1),
                     .const (BitVec.ofNat 64 0),
                     .var .local (ofString "is"),
                     .var .local (ofString "isz"),
                     .var .local (ofString "os"),
                     .var .local (ofString "osz"),
                     .rfield 0 (.var .local (ofString "code")),
                     .rfield 1 (.var .local (ofString "code")),
                     .rfield 0 (.var .local (ofString "dl")),
                     .const (BitVec.ofNat 64 0)]))))))
        callcodeContProg_g10) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_assoc ?_
    refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_stack_push)
      (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgpins, hR_cp⟩ := hQc
      rw [evmR_entry_eq_g10] at hR_cp
      exact CcR2Q_res_g10 hR_cp hp
    · refine seq_dec_swap_g10 (callcodeCont_noread_g10 (by decide)) ?_
      refine HandlerRunA.dec_carry_g10 (fun t v hp => CcR2Q_setVar_g10 (by decide) hp) ?_
      refine HandlerRunA.seq_assoc ?_
      refine HandlerRunA.seq_set_retdata_empty (P := fun t => CcR2Q_g10 s0 t)
        (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_
      · intro t cpost hi hw hp hi_cp hw_cp hch_cp hglob_cp hevR_cp hbe hmem
        exact CcR2Q_res_g10 (le_of_eq hevR_cp) hp
      · refine HandlerRunA.seq_assoc ?_
        refine HandlerRunA.seq_store_ev64_charged_g10 (P := fun t => CcR2Q_g10 s0 t)
          (Q := fun _ => True) ?_ ?_ ?_
        · intro t v hp hv
          obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := hp
          obtain ⟨w', hwv, hwK⟩ := eval_store64_add_g10 hmcg hv
          exact ⟨w', hwv⟩
        · intro t w heval hi hw hp hR_lt
          obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := hp
          obtain ⟨w', hwv, hwK⟩ := eval_store64_add_g10 hmcg heval
          injection hwv with hwv1
          injection hwv1 with hwv2
          subst hwv2
          obtain ⟨hInv1, hWF1, hch1, hR1⟩ :=
            ev64_store_evmStep_g10 (s0 := s0) (K := w1.toNat) hi hw hwK hcredit
              (evmInv_gas_top_g10 hInvS)
          exact ⟨hInv1, hWF1, hch1, trivial, hR1⟩
        · refine HandlerRunA.seq_store_ev_off_charged_g10 (off := 72)
            (P := fun _ => True) (Q := fun _ => True) (by omega) ?_ ?_ ?_
          · intro t v hp hv
            exact eval_op_word_g10 BinOp.add _ v hv
          · intro t w heval hi hw hp hR_lt
            obtain ⟨hInv1, hWF1, hch1, hRle⟩ :=
              evOff_store_evmStep_g10 (Q := fun _ => True) t w 72 (Or.inr rfl) hi hw
            exact ⟨hInv1, hWF1, hch1, trivial, lt_of_le_of_lt hRle hR_lt⟩
          · exact callcodeCont_run_g10
  · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "is") (by decide)) ?_
    refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      exact CcR2Q_setVarRes_g10 (by decide)
        (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
    · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "isz") (by decide)) ?_
      refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
      · intro t values body' callee ret' hc hi hw hp hargs hl
        exact trivial
      · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
        exact CcR2Q_setVarRes_g10 (by decide)
          (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
      · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "os") (by decide)) ?_
        refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
        · intro t values body' callee ret' hc hi hw hp hargs hl
          exact trivial
        · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
          exact CcR2Q_setVarRes_g10 (by decide)
            (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
        · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "osz") (by decide)) ?_
          refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
          · intro t values body' callee ret' hc hi hw hp hargs hl
            exact trivial
          · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
            exact CcR2Q_setVarRes_g10 (by decide)
              (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
          · exact callcodeGenericCall2_r32 hgc32

theorem callcodeCode2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
        [.var .local (ofString "code_address")] cont) := by
  refine HandlerRunA.decCall hW.epsA_ext_code_of (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hgk, hRev, hm32⟩ := hQc
    have hRr : evmR (setVarHOLFinite (ofString "code") v { cpost with locals := t.locals })
        = evmR cpost := (evm_congr (s := cpost)
          (t := setVarHOLFinite (ofString "code") v { cpost with locals := t.locals }) rfl rfl).2.1
    refine CcDLQ_lu_g10 (lu6_setVarRes_ne_g10 t cpost (ofString "code") v (by decide)) ?_ ?_ ?_ hp
    · exact le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10))
    · exact (globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)
    · exact hm32

theorem callcodeDlIte2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
            (.const (BitVec.ofNat 64 0)))
          (.seq (.call (some (none, none)) (ofString "charge_gas")
              [.rfield 2 (.var .local (ofString "dl"))])
            (.call (some (none, none)) (ofString "warm_address")
              [.var .local (ofString "code_address")]))
          .skip)
        cont) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_assoc ?_
    refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_charge_gas_keep32)
      (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨⟨hglob_cp, hmem32⟩, hR_cp⟩ := hQc
      have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
        (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
      rw [evmR_entry_eq_g10] at hR_cp
      refine CcDLQ_lu_g10 (t := t) (r := { cpost with locals := t.locals })
        (fun nm' _ => rfl) ?_ ?_ ?_ hp
      · rw [hRr]; exact hR_cp
      · exact globN_congr_g10 hglob_cp "ev"
      · exact hmem32
    · refine HandlerRunA.seq_call Group10.epsA_warm_address_keep32_g10
        (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ ?_
      · intro t values body' callee ret' hc hi hw hp hargs hl
        exact trivial
      · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
        obtain ⟨hgk, hRev, hm32⟩ := hQc
        have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
          (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
        refine CcDLQ_lu_g10 (t := t) (r := { cpost with locals := t.locals })
          (fun nm' _ => rfl) ?_ ?_ ?_ hp
        · exact le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10))
        · exact (globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)
        · exact hm32
      · exact hcont
  · exact HandlerRunA.seq_skip hcont

theorem callcodeCodeAddr2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
        (.seq
          (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
              (.const (BitVec.ofNat 64 0)))
            (.seq (.call (some (none, none)) (ofString "charge_gas")
                [.rfield 2 (.var .local (ofString "dl"))])
              (.call (some (none, none)) (ofString "warm_address")
                [.var .local (ofString "code_address")]))
            .skip)
          cont)) :=
  HandlerRunA.dec_carry_g10 (fun t v hp => CcDLQ_setVar_g10 (by decide) hp)
    (callcodeDlIte2_r32 hW hcont)

theorem callcodeDl2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost")
        [.var .local (ofString "code_address0")] cont) := by
  refine HandlerRunA.decCall (epsA_cdc_full_g10 hW) (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hpins, hRev, d0, d1, d2, hv, hdc1, hdc2⟩ := hQc
    obtain ⟨hgev, hm32, _⟩ := hpins v rfl
    have hRr : evmR (setVarHOLFinite (ofString "dl") v { cpost with locals := t.locals })
        = evmR cpost := (evm_congr (s := cpost)
          (t := setVarHOLFinite (ofString "dl") v { cpost with locals := t.locals }) rfl rfl).2.1
    refine ⟨CcPQ_lu5_g10 (lu5_setVarRes_ne_g10 t cpost (ofString "dl") v (by decide))
      (by rw [hRr, hRev, evmR_entry_eq_g10]) hgev hm32 hp, d0, d1, d2, ?_, hdc1, hdc2⟩
    dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    first | rw [if_pos rfl, hv] | simp [hv]

theorem callcodeWarmIte2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address")
            [.var .local (ofString "code_address0")])
          .skip)
        cont) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_call Group10.epsA_warm_address_keep32_g10
      (Q := fun t => CcPQ_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgk, hRev, hm32⟩ := hQc
      have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
        (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
      exact CcPQ_lu5_g10 (t := t) (r := { cpost with locals := t.locals })
        (fun nm' _ => rfl)
        (le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10)))
        ((globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)) hm32 hp
    · exact hcont
  · exact HandlerRunA.seq_skip hcont

theorem op_callcode_tail2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32)
 :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true callcodeTailProg_g10 := by
  simp only [callcodeTailProg_g10]
  exact callcodeWarmIte2_r32 hW
    (callcodeDl2_r32 hW
      (callcodeCodeAddr2_r32 hW
        (callcodeCode2_r32 hW
          (callcodeGw_g10
            (callcodeMcg_g10
              (callcodeChargeMcg_g10
                (callcodeStore184_g10
                  (callcodeExtend_g10
                    (callcodeReservoir_g10
                      (callcodeStore72z_g10
                        (callcodeSender2_r32 hW
                          (callcodeInsufficient2_r32
                            (callcodeStarted2_r32
                              (callcodeInsfTail2_r32 hgc32))))))))))))))

theorem op_callcode_run_full2_r32 (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32)
 {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (sourceFnBody Guest.Software.guestFn_op_callcode) :=
  op_callcode_prefix_g10 (op_callcode_tail2_r32 hW hgc32)

/-! ## `op_call` under the child-push contract -/
theorem callWarmIte2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address")
            [.var .local (ofString "to")])
          .skip)
        cont) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_call Group10.epsA_warm_address_keep32_g10
      (Q := fun t => CcPQ_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgk, hRev, hm32⟩ := hQc
      have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
        (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
      exact CcPQ_lu5_g10 (t := t) (r := { cpost with locals := t.locals })
        (fun nm' _ => rfl)
        (le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10)))
        ((globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)) hm32 hp
    · exact hcont
  · exact HandlerRunA.seq_skip hcont

theorem callDl2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.decCall (ofString "dl") (.comb [.one, .one, .one])
          (ofString "calculate_delegation_cost")
        [.var .local (ofString "to")] cont) := by
  refine HandlerRunA.decCall (epsA_cdc_full_g10 hW) (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hpins, hRev, d0, d1, d2, hv, hdc1, hdc2⟩ := hQc
    obtain ⟨hgev, hm32, _⟩ := hpins v rfl
    have hRr : evmR (setVarHOLFinite (ofString "dl") v { cpost with locals := t.locals })
        = evmR cpost := (evm_congr (s := cpost)
      (t := setVarHOLFinite (ofString "dl") v { cpost with locals := t.locals }) rfl rfl).2.1
    refine ⟨CcPQ_lu5_g10 (lu5_setVarRes_ne_g10 t cpost (ofString "dl") v (by decide))
      (by rw [hRr, hRev, evmR_entry_eq_g10]) hgev hm32 hp, d0, d1, d2, ?_, hdc1, hdc2⟩
    dsimp only [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    first | rw [if_pos rfl, hv] | simp [hv]

theorem callSender2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsA)
     {cont : ProgHOL 64}
    (hcont : HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true cont) :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.decCall (ofString "sender") .one (ofString "get_account")
        [.load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 32)])]
        cont) := by
  refine HandlerRunA.decCall hW.epsA_get_account (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ hcont
  · intro t values body' callee ret' hc hi hw hp hargs hl
    exact trivial
  · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
    obtain ⟨hgk, hRev⟩ := hQc
    exact CcR2Q_setVarRes_g10 (by decide) (le_of_eq (hRev.trans evmR_entry_eq_g10)) hp

theorem callGenericCall2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc32 : callSpec_generic_call_r32)
 :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq
        (.call (some (some (.local, ofString "started"), none)) (ofString "generic_call")
          [.rfield 1 (.var .local (ofString "mcg")),
           .var .local (ofString "reservoir"),
           .var .local (ofString "value"),
           .load .one (.op .add [.var .local (ofString "msg"), .const (BitVec.ofNat 64 32)]),
           .var .local (ofString "to"),
           .var .local (ofString "code_address"),
           .const (BitVec.ofNat 64 1),
           .const (BitVec.ofNat 64 0),
           .var .local (ofString "is"),
           .var .local (ofString "isz"),
           .var .local (ofString "os"),
           .var .local (ofString "osz"),
           .rfield 0 (.var .local (ofString "code")),
           .rfield 1 (.var .local (ofString "code")),
           .rfield 0 (.var .local (ofString "dl")),
           .var .local (ofString "new_account_charged")])
        callcodeContProg_g10) :=
  HandlerRunA.seq_call_childCall_r32 hgc32
    (fun t values body callee retShape v cpost hi hw hp hargs hl hshp hi_cp hw_cp hch_cp hQc =>
      CcR2Q_setVarRes_g10 (by decide)
        (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp)
    (fun t ht => by
      obtain ⟨w0, w1, hmcg, hcredit, -⟩ := ht
      have h' : R11Shards.OpDispatchSpec.evmR t + w1.toNat + 1 ≤
          R11Shards.OpDispatchSpec.evmR s0 := hcredit
      omega)
    (HandlerRunA.weaken (fun t ht hp => trivial) callcodeCont_run_g10)
theorem callInsfTail2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hgc32 : callSpec_generic_call_r32)
 :
    HandlerRunA s0 (fun t => CcR2Q_g10 s0 t) true
      (.seq
        (.ite (.cmp .notEqual (.var .local (ofString "insufficient"))
            (.const (BitVec.ofNat 64 0)))
          (.seq (.call (some (none, none)) (ofString "stack_push")
              [.rstruct [.const (0#64), .const (0#64), .const (0#64), .const (0#64)]])
            (.dec (ofString "empty") .one (.var .global (ofString "evm_empty"))
              (.seq (.call (some (none, none)) (ofString "set_retdata")
                  [.var .local (ofString "empty"), .const (BitVec.ofNat 64 0)])
                (.seq (.store (.op .add [.var .global (ofString "ev"),
                      .const (BitVec.ofNat 64 64)])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"),
                         .const (BitVec.ofNat 64 64)]),
                       .rfield 1 (.var .local (ofString "mcg"))]))
                  (.seq (.store (.op .add [.var .global (ofString "ev"),
                      .const (BitVec.ofNat 64 72)])
                    (.op .add
                      [.load .one (.op .add [.var .global (ofString "ev"),
                         .const (BitVec.ofNat 64 72)]),
                       .var .local (ofString "reservoir")]))
                    (.ite (.cmp .notEqual (.var .local (ofString "new_account_charged"))
                        (.const (BitVec.ofNat 64 0)))
                      (.call (some (none, none)) (ofString "credit_state_gas_refund")
                        [.const (BitVec.ofNat 64 183600)])
                      .skip))))))
          (.decCall (ofString "is") .one (ofString "sat_word")
            [.var .local (ofString "in_start")]
            (.decCall (ofString "isz") .one (ofString "sat_word")
              [.var .local (ofString "in_size")]
              (.decCall (ofString "os") .one (ofString "sat_word")
                [.var .local (ofString "out_start")]
                (.decCall (ofString "osz") .one (ofString "sat_word")
                  [.var .local (ofString "out_size")]
                  (.call (some (some (.local, ofString "started"), none))
                    (ofString "generic_call")
                    [.rfield 1 (.var .local (ofString "mcg")),
                     .var .local (ofString "reservoir"),
                     .var .local (ofString "value"),
                     .load .one (.op .add [.var .local (ofString "msg"),
                       .const (BitVec.ofNat 64 32)]),
                     .var .local (ofString "to"),
                     .var .local (ofString "code_address"),
                     .const (BitVec.ofNat 64 1),
                     .const (BitVec.ofNat 64 0),
                     .var .local (ofString "is"),
                     .var .local (ofString "isz"),
                     .var .local (ofString "os"),
                     .var .local (ofString "osz"),
                     .rfield 0 (.var .local (ofString "code")),
                     .rfield 1 (.var .local (ofString "code")),
                     .rfield 0 (.var .local (ofString "dl")),
                     .var .local (ofString "new_account_charged")]))))))
        callcodeContProg_g10) := by
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine HandlerRunA.seq_assoc ?_
    refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_stack_push)
      (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgpins, hR_cp⟩ := hQc
      rw [evmR_entry_eq_g10] at hR_cp
      exact CcR2Q_res_g10 hR_cp hp
    · refine seq_dec_swap_g10 (callcodeCont_noread_g10 (by decide)) ?_
      refine HandlerRunA.dec_carry_g10 (fun t v hp => CcR2Q_setVar_g10 (by decide) hp) ?_
      refine HandlerRunA.seq_assoc ?_
      refine HandlerRunA.seq_set_retdata_empty (P := fun t => CcR2Q_g10 s0 t)
        (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_
      · intro t cpost hi hw hp hi_cp hw_cp hch_cp hglob_cp hevR_cp hbe hmem
        exact CcR2Q_res_g10 (le_of_eq hevR_cp) hp
      · refine HandlerRunA.seq_assoc ?_
        refine HandlerRunA.seq_store_ev64_charged_g10 (P := fun t => CcR2Q_g10 s0 t)
          (Q := fun _ => True) ?_ ?_ ?_
        · intro t v hp hv
          obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := hp
          obtain ⟨w', hwv, hwK⟩ := eval_store64_add_g10 hmcg hv
          exact ⟨w', hwv⟩
        · intro t w heval hi hw hp hR_lt
          obtain ⟨w0, w1, hmcg, hcredit, hInvS⟩ := hp
          obtain ⟨w', hwv, hwK⟩ := eval_store64_add_g10 hmcg heval
          injection hwv with hwv1
          injection hwv1 with hwv2
          subst hwv2
          obtain ⟨hInv1, hWF1, hch1, hR1⟩ :=
            ev64_store_evmStep_g10 (s0 := s0) (K := w1.toNat) hi hw hwK hcredit
              (evmInv_gas_top_g10 hInvS)
          exact ⟨hInv1, hWF1, hch1, trivial, hR1⟩
        · refine HandlerRunA.seq_assoc ?_
          refine HandlerRunA.seq_store_ev_off_charged_g10 (off := 72)
            (P := fun _ => True) (Q := fun _ => True) (by omega) ?_ ?_ ?_
          · intro t v hp hv
            exact eval_op_word_g10 BinOp.add _ v hv
          · intro t w heval hi hw hp hR_lt
            obtain ⟨hInv1, hWF1, hch1, hRle⟩ :=
              evOff_store_evmStep_g10 (Q := fun _ => True) t w 72 (Or.inr rfl) hi hw
            exact ⟨hInv1, hWF1, hch1, trivial, lt_of_le_of_lt hRle hR_lt⟩
          · refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
            · exact HandlerRunA.seq_call epsA_credit_state_gas_refund
                (Q := fun _ => True)
                (fun t values body' callee ret' hc hi hw hp hargs hl => trivial)
                (fun t values body callee retShape v cpost hi hw hp hargs hl
                    hi_cp hw_cp hch_cp hQc => trivial)
                callcodeCont_run_g10
            · exact HandlerRunA.seq_skip callcodeCont_run_g10
  · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "is") (by decide)) ?_
    refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      exact CcR2Q_setVarRes_g10 (by decide)
        (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
    · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "isz") (by decide)) ?_
      refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
      · intro t values body' callee ret' hc hi hw hp hargs hl
        exact trivial
      · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
        exact CcR2Q_setVarRes_g10 (by decide)
          (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
      · refine seq_decCall_swap_g10 (callcodeCont_noread_g10 (nm := ofString "os") (by decide)) ?_
        refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
        · intro t values body' callee ret' hc hi hw hp hargs hl
          exact trivial
        · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
          exact CcR2Q_setVarRes_g10 (by decide)
            (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
        · refine seq_decCall_swap_g10
            (callcodeCont_noread_g10 (nm := ofString "osz") (by decide)) ?_
          refine HandlerRunA.decCall epsA_sat_word (Q := fun t => CcR2Q_g10 s0 t) ?_ ?_ ?_
          · intro t values body' callee ret' hc hi hw hp hargs hl
            exact trivial
          · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
            exact CcR2Q_setVarRes_g10 (by decide)
              (le_of_eq ((evmR_congr_full_g10 hQc).trans evmR_entry_eq_g10)) hp
          · exact callGenericCall2_r32 hgc32

theorem callNacBlock2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsCall_g10)
    (hgc32 : callSpec_generic_call_r32)
 :
    HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true
      (.dec (ofString "new_account_charged") .one (.const (BitVec.ofNat 64 0))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "vz")) (.const (BitVec.ofNat 64 0)))
            (.decCall (ofString "alive") .one (ofString "is_account_alive")
              [.var .local (ofString "to")]
              (.ite (.cmp .equal (.var .local (ofString "alive"))
                  (.const (BitVec.ofNat 64 0)))
                (.seq (.assign .local (ofString "new_account_charged")
                    (.const (BitVec.ofNat 64 1)))
                  (.call (some (none, none)) (ofString "charge_state_gas")
                    [.const (BitVec.ofNat 64 183600)]))
                .skip))
            .skip)
          callRestProg_g10)) := by
  have hrest : HandlerRunA s0 (fun t => CcDLQ_g10 s0 t) true callRestProg_g10 := by
    simp only [callRestProg_g10]
    exact callcodeGw_g10
      (callcodeMcg_g10
        (callcodeChargeMcg_g10
          (callcodeStore184_g10
            (callcodeExtend_g10
              (callcodeReservoir_g10
                (callcodeStore72z_g10
                  (callSender2_r32 hW.toWorldAccountSpecsA
                    (callcodeInsufficient2_r32
                      (callcodeStarted2_r32
                        (callInsfTail2_r32 hgc32))))))))))
  refine HandlerRunA.dec_carry_g10 (fun t v hp => CcDLQ_setVar_g10 (by decide) hp) ?_
  refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
  · refine seq_decCall_swap_g10 (contNoreadP_to_g10 callRestNoread_g10) ?_
    refine HandlerRunA.decCall hW.epsA_is_account_alive_k32
      (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ ?_
    · intro t values body' callee ret' hc hi hw hp hargs hl
      exact trivial
    · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
      obtain ⟨hgk, hRev, hm32⟩ := hQc
      have hRr : evmR (setVarHOLFinite (ofString "alive") v { cpost with locals := t.locals })
          = evmR cpost := (evm_congr (s := cpost)
        (t := setVarHOLFinite (ofString "alive") v { cpost with locals := t.locals }) rfl rfl).2.1
      refine CcDLQ_lu_g10
        (lu6_setVarRes_ne_g10 t cpost (ofString "alive") v (by decide)) ?_ ?_ ?_ hp
      · exact le_of_eq (hRr.trans (hRev.trans evmR_entry_eq_g10))
      · exact (globN_of_lookup_eq_g10 "ev" (hgk (ofString "ev") (by decide)).symm)
      · exact hm32
    · refine HandlerRunA.seq_ite_unit (fun t w heval hw0 => ?_) (fun t heval => ?_)
      · refine HandlerRunA.seq_assoc ?_
        refine HandlerRunA.seq_assign_local
          (fun t v hv hi hp => CcDLQ_setVar_g10 (by decide) hp) ?_
        refine HandlerRunA.seq_call (epsA_keepR_g10 epsA_charge_state_gas_k32)
          (Q := fun t => CcDLQ_g10 s0 t) ?_ ?_ ?_
        · intro t values body' callee ret' hc hi hw hp hargs hl
          exact trivial
        · intro t values body callee retShape v cpost hi hw hp hargs hl hi_cp hw_cp hch_cp hQc
          obtain ⟨⟨hglob_cp, hmem32⟩, hR_cp⟩ := hQc
          have hRr : evmR { cpost with locals := t.locals } = evmR cpost :=
            (evm_congr (s := cpost) (t := { cpost with locals := t.locals }) rfl rfl).2.1
          rw [evmR_entry_eq_g10] at hR_cp
          refine CcDLQ_lu_g10 (t := t) (r := { cpost with locals := t.locals })
            (fun nm' _ => rfl) ?_ ?_ ?_ hp
          · rw [hRr]; exact hR_cp
          · exact globN_congr_g10 hglob_cp "ev"
          · exact hmem32
        · exact hrest
      · exact HandlerRunA.seq_skip hrest
  · exact HandlerRunA.seq_skip hrest

theorem op_call_tail2_r32 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hW : WorldAccountSpecsCall_g10)
    (hgc32 : callSpec_generic_call_r32)
 :
    HandlerRunA s0 (fun t => CcPQ_g10 s0 t) true
      (.seq
        (.ite (.cmp .equal (.var .local (ofString "warm")) (.const (BitVec.ofNat 64 0)))
          (.call (some (none, none)) (ofString "warm_address")
            [.var .local (ofString "to")])
          .skip)
        (.decCall (ofString "dl") (.comb [.one, .one, .one])
            (ofString "calculate_delegation_cost")
          [.var .local (ofString "to")]
          (.dec (ofString "code_address") .one (.rfield 1 (.var .local (ofString "dl")))
            (.seq
              (.ite (.cmp .notEqual (.rfield 0 (.var .local (ofString "dl")))
                  (.const (BitVec.ofNat 64 0)))
                (.seq (.call (some (none, none)) (ofString "charge_gas")
                    [.rfield 2 (.var .local (ofString "dl"))])
                  (.call (some (none, none)) (ofString "warm_address")
                    [.var .local (ofString "code_address")]))
                .skip)
              (.decCall (ofString "code") (.comb [.one, .one]) (ofString "ext_code_of")
                [.var .local (ofString "code_address")]
                (.dec (ofString "new_account_charged") .one (.const (BitVec.ofNat 64 0))
                  (.seq
                    (.ite (.cmp .equal (.var .local (ofString "vz"))
                        (.const (BitVec.ofNat 64 0)))
                      (.decCall (ofString "alive") .one (ofString "is_account_alive")
                        [.var .local (ofString "to")]
                        (.ite (.cmp .equal (.var .local (ofString "alive"))
                            (.const (BitVec.ofNat 64 0)))
                          (.seq (.assign .local (ofString "new_account_charged")
                              (.const (BitVec.ofNat 64 1)))
                            (.call (some (none, none)) (ofString "charge_state_gas")
                              [.const (BitVec.ofNat 64 183600)]))
                          .skip))
                      .skip)
                    callRestProg_g10))))))) :=
  callWarmIte2_r32
    (callDl2_r32 hW.toWorldAccountSpecsA
      (callcodeCodeAddr2_r32 hW.toWorldAccountSpecsA
        (callcodeCode2_r32 hW.toWorldAccountSpecsA
          (callNacBlock2_r32 hW hgc32))))

theorem op_call_run_full2_r32 (hW : WorldAccountSpecsCall_g10)
    (hgc32 : callSpec_generic_call_r32)
 {F : Type} (s0 : PanSemStateFiniteExact 64 F) :
    HandlerRunA s0 (fun _ => EvmInv s0) false
      (sourceFnBody Guest.Software.guestFn_op_call) :=
  op_call_prefix_g10 (op_call_tail2_r32 hW hgc32)

/-! ## The R32 continuations bundle and the unconditional call specs -/

/-- The four call-handler continuations hold under the true child-push
`generic_call` contract alone: `op_call` and `op_callcode` through the rebuilt
tail walks above, `op_delegatecall` and `op_staticcall` through the walks of
`Group10CallGenR32`. -/
theorem group10CallR32Continuations (hgc32 : callSpec_generic_call_r32) :
    Group10CallR32Continuations where
  op_call s0 hWc := op_call_run_full2_r32 hWc hgc32 s0
  op_callcode hW s0 := op_callcode_run_full2_r32 hW hgc32 s0
  op_delegatecall s0 hW := op_delegatecall_run_full_r32 s0 hW hgc32
  op_staticcall s0 hW := op_staticcall_run_full_r32 s0 hW hgc32

/-- The R32 call world: the compiled call-family world record strengthened
with the true child-push `generic_call` contract in place of the unsound
chain-preserving assumption. -/
structure WorldAccountSpecsCall_g10R32 extends WorldAccountSpecsCall_g10 where
  gc : callSpec_generic_call_r32

/-- `op_call` (guest AST index 603) closed unconditionally over the R32 call
world. -/
theorem op_call_specA_r32_gc (hWc : WorldAccountSpecsCall_g10R32) :
    OpHandlerSpecA (ofString "op_call") :=
  op_call_specA_r32 hWc.toWorldAccountSpecsCall_g10 (group10CallR32Continuations hWc.gc)

/-- `op_callcode` (guest AST index 604) closed unconditionally over the world
record and the child-push contract. -/
theorem op_callcode_specA_r32_gc (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    OpHandlerSpecA (ofString "op_callcode") :=
  op_callcode_specA_r32 hW (group10CallR32Continuations hgc32)

/-- `op_delegatecall` (guest AST index 605) closed unconditionally over the
world record and the child-push contract. -/
theorem op_delegatecall_specA_r32_gc (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    OpHandlerSpecA (ofString "op_delegatecall") :=
  op_delegatecall_specA_r32 hW (group10CallR32Continuations hgc32)

/-- `op_staticcall` (guest AST index 606) closed unconditionally over the
world record and the child-push contract. -/
theorem op_staticcall_specA_r32_gc (hW : WorldAccountSpecsA)
    (hgc32 : callSpec_generic_call_r32) :
    OpHandlerSpecA (ofString "op_staticcall") :=
  op_staticcall_specA_r32 hW (group10CallR32Continuations hgc32)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
