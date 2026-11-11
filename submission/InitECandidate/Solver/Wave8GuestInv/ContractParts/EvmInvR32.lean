import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterChainCutover
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

/-! # R32 Invariants and Chain-WF Cutover `op_dispatch` Router (`EvmInvR32`)

R32 replaces the R31 statement bundles' (false) `EvmInv`-universal premises —
`hdb : ∀ s, EvmInv s → WitnessDbOK s` and `hsys : ∀ s, EvmInv s → Inside …` — with
honest guarded facts:

* `EvmInvR32 s := EvmInv s ∧ StorageCreateFinish.WitnessDbOK s ∧
  Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")` — the
  EVM-frame invariant strengthened with the witness-DB well-formedness established by
  the `GbodyRunAttempt` lane and the `vm_system_address` heap materialization
  (`evm_init` allocates it on the heap; `FixedTyped` alone cannot recover it, so it is
  carried explicitly per the R32 design note).
* `WorldOKR32 s := WorldOK s ∧ (globN s "ws" ≠ 0 → NodeDbSlicesBounded s (memW s (globN s "ws")))`
  — the world invariant strengthened with the witness-DB slice boundedness established
  by the `WkProcessTransaction` R32 lane.

This module defines the R32 spec vocabulary (`OpHandlerChainSpecR32`,
`OpPushBoundedChainSpecR32`, `OpLogBoundedChainSpecR32`, `OpDispatchSpecAR32`,
`OpDispatchChainHandlersCutoverR32`) and replays the chain-WF cutover `op_dispatch`
router of `R16Shards.OpHandlersB.RouterChainCutover` at `EvmInvR32` strength:
`op_dispatch_chain_spec_cutover_r32` reduces `OpDispatchSpecAR32` to the 87-field
`OpDispatchChainHandlersCutoverR32` bundle. The only genuinely new ingredients are the
congruence lemmas `localsFree_evmInvR32` (via `localsFree_evmInv` +
`StorageCreateFinish.witnessDbOK_with_locals_clock`), `evmChainRunR32_callEntry`, and
`opDispatchChainPostR32_congr_lc`; everything else is the R16 router replayed verbatim
with `EvmInv` replaced by `EvmInvR32`. The 87 handler fields are sibling obligations
(the R32 chain-handler lane); nothing here assumes them. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open Flapjack.Compiler.Encoders.Asm
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterAligned
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. R32 invariants -/

/-- R32 EVM invariant: `EvmInv` plus witness-DB well-formedness plus the
`vm_system_address` heap materialization. -/
def EvmInvR32 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  EvmInv s ∧ StorageCreateFinish.WitnessDbOK s ∧
    Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")

/-- R32 world invariant: `WorldOK` plus witness-DB slice boundedness when `ws ≠ 0`. -/
def WorldOKR32 {F : Type} (s : PanSemStateFiniteExact 64 F) : Prop :=
  WorldOK s ∧ (globN s "ws" ≠ 0 → StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))

theorem EvmInvR32.of_evmInv {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hdb : StorageCreateFinish.WitnessDbOK s)
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    EvmInvR32 s :=
  ⟨hInv, hdb, hsys⟩

theorem EvmInvR32.evmInv {F : Type} {s : PanSemStateFiniteExact 64 F} (h : EvmInvR32 s) :
    EvmInv s := h.1

theorem EvmInvR32.witnessDbOK {F : Type} {s : PanSemStateFiniteExact 64 F} (h : EvmInvR32 s) :
    StorageCreateFinish.WitnessDbOK s := h.2.1

theorem EvmInvR32.sysInside {F : Type} {s : PanSemStateFiniteExact 64 F} (h : EvmInvR32 s) :
    Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr") := h.2.2

theorem WorldOKR32.worldOK {F : Type} {s : PanSemStateFiniteExact 64 F} (h : WorldOKR32 s) :
    WorldOK s := h.1

theorem WorldOKR32.nodeDbSlicesBounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : WorldOKR32 s) (hnz : globN s "ws" ≠ 0) :
    StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")) := h.2 hnz

/-- `EvmInvR32` is free in locals and clock (`localsFree_evmInv` +
`StorageCreateFinish.witnessDbOK_with_locals_clock`; the `Inside` conjunct only reads
globals, so it transfers definitionally). -/
theorem localsFree_evmInvR32 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (k : Nat) (h : EvmInvR32 s) :
    EvmInvR32 { s with locals := L, clock := k } :=
  ⟨localsFree_evmInv s L k h.1, StorageCreateFinish.witnessDbOK_with_locals_clock h.2.1 L k,
    h.2.2⟩

/-! ## 2. R32 chain-WF post and handler specs -/

/-- Postcondition of the R32 `op_dispatch` contract on initial state `s`. -/
def OpDispatchChainPostR32 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ((∃ v, r = some (.returned v)) →
    (EvmInvR32 post ∧ HeadMemBridge.HeadMemChainWF post) ∧ evmPot post < evmPot s) ∧
  (IsEvmErr r →
    (EvmInvR32 post ∧ HeadMemBridge.HeadMemChainWF post) ∧
      (evmChain post).length = (evmChain s).length ∧
      Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s)

/-- R32 opcode handler spec: `EvmInvR32`-guarding `OpHandlerChainSpec`. -/
def OpHandlerChainSpecR32 (fname : MlS) : Prop :=
  FunSpec (fun s => EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
    OpDispatchChainPostR32 fname

/-- R32 bounded `op_push` (`nbytes ≤ 32`) carrying `HeadMemChainWF` and `EvmInvR32`. -/
def OpPushBoundedChainSpecR32 : Prop :=
  FunSpec
    (fun s => (EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nbytes") = some (.val (.word n)) ∧ n.toNat ≤ 32)
    OpDispatchChainPostR32
    (ofString "op_push")

/-- R32 bounded `op_log` (`ntopics ≤ 4`) carrying `HeadMemChainWF` and `EvmInvR32`. -/
def OpLogBoundedChainSpecR32 : Prop :=
  FunSpec
    (fun s => (EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) ∧
      ∃ nt : BitVec 64, s.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4)
    OpDispatchChainPostR32
    (ofString "op_log")

/-- R32 aligned `op_dispatch` contract (`OpDispatchSpecA` with `EvmInvR32`). -/
def OpDispatchSpecAR32 : Prop :=
  FunSpec (fun s => EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
    (fun s r post =>
      ((∃ v, r = some (.returned v)) →
        (EvmInvR32 post ∧ HeadMemBridge.HeadMemChainWF post) ∧ evmPot post < evmPot s) ∧
      (IsEvmErr r → (EvmInvR32 post ∧ HeadMemBridge.HeadMemChainWF post) ∧
        (evmChain post).length = (evmChain s).length ∧
        Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s))
    (ofString "op_dispatch")

theorem opDispatchChainPostR32_other {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hnret : ∀ v, r ≠ some (.returned v)) (hnerr : ¬ IsEvmErr r) :
    OpDispatchChainPostR32 s r t :=
  ⟨fun ⟨v, hv⟩ => (hnret v hv).elim, fun he => (hnerr he).elim⟩

theorem opDispatchChainPostR32_error {F : Type} (s t : PanSemStateFiniteExact 64 F) :
    OpDispatchChainPostR32 s (some .error) t :=
  opDispatchChainPostR32_other (by intro _ h; cases h) (by rintro ⟨_, h⟩; cases h)

theorem opDispatchChainPostR32_congr_lc {F : Type} {s s' post post' : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hs_m : s'.memory = s.memory) (hs_g : s'.globals = s.globals)
    (hp_m : post'.memory = post.memory) (hp_g : post'.globals = post.globals)
    (hp_lc : post' = { post with locals := post'.locals, clock := post'.clock })
    (h : OpDispatchChainPostR32 s' r post) :
    OpDispatchChainPostR32 s r post' := by
  have hcs := evm_congr hs_m hs_g
  have hcp := evm_congr hp_m hp_g
  have hInv (hi : EvmInvR32 post) : EvmInvR32 post' := by
    rw [hp_lc]; exact localsFree_evmInvR32 post _ _ hi
  have hWF (hw : HeadMemBridge.HeadMemChainWF post) : HeadMemBridge.HeadMemChainWF post' :=
    (HeadMemBridge.headMemChainWF_congr hp_m hp_g).mpr hw
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨⟨hi, hw⟩, hpot⟩ := h.1 hret
    exact ⟨⟨hInv hi, hWF hw⟩, by rw [hcp.1, ← hcs.1]; exact hpot⟩
  · obtain ⟨⟨hi, hw⟩, hlen, hR⟩ := h.2 herr
    have hRs : Wave8GuestInv.evmR s' = Wave8GuestInv.evmR s := hcs.2.1
    have hRp : Wave8GuestInv.evmR post' = Wave8GuestInv.evmR post := hcp.2.1
    exact ⟨⟨hInv hi, hWF hw⟩, by rw [hcp.2.2.1, ← hcs.2.2.1]; exact hlen,
      by rw [hRp, ← hRs]; exact hR⟩

/-! ## 3. R32 walk combinators -/

structure DispatchSpecWalkCR32 (p : ProgHOL 64) : Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode →
    (EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) →
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none →
      (evaluateHOLFiniteState s p).2 = s) ∧
    ((evaluateHOLFiniteState s p).1 ≠ none →
      OpDispatchChainPostR32 s (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2)

theorem DispatchSpecWalkCR32.skip : DispatchSpecWalkCR32 .skip := by
  refine ⟨fun s _ _ _ => ?_⟩
  rw [evaluateHOLFiniteState_skip]
  exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

theorem DispatchSpecWalkCR32.raise (e : ExpHOL 64) :
    DispatchSpecWalkCR32 (.raise (ofString "EvmErr") e) := by
  refine ⟨fun {F} s _ hRun _ => ⟨fun hn => (raise_ne_none s _ e hn).elim, fun _ => ?_⟩⟩
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · refine ⟨?_, fun _ => ?_⟩
      · rintro ⟨_, h⟩; cases h
      · have hInv' : EvmInvR32 (emptyLocalsHOLFinite s) :=
          localsFree_evmInvR32 s (emptyLocalsHOLFinite s).locals s.clock hRun.1
        have hWF' : HeadMemBridge.HeadMemChainWF (emptyLocalsHOLFinite s) :=
          HeadMemBridge.headMemChainWF_locals s (emptyLocalsHOLFinite s).locals s.clock hRun.2.1
        have hcongr := evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
        have hR : Wave8GuestInv.evmR (emptyLocalsHOLFinite s) ≤ Wave8GuestInv.evmR s :=
          le_of_eq hcongr.2.1
        exact ⟨⟨hInv', hWF'⟩, hcongr.2.2.1, hR⟩
    · exact opDispatchChainPostR32_error s s
  · exact opDispatchChainPostR32_error s s

theorem DispatchSpecWalkCR32.seqRaiseReturn (e1 e2 : ExpHOL 64) :
    DispatchSpecWalkCR32 (.seq (.raise (ofString "EvmErr") e1) (.return e2)) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr : evaluateHOLFiniteState s (.raise (ofString "EvmErr") e1) with ⟨r, mid⟩
  simp only [hr] at hnt ⊢
  cases r with
  | none =>
    have hnn := raise_ne_none s (ofString "EvmErr") e1
    rw [hr] at hnn
    exact (hnn rfl).elim
  | some _ =>
    have h1 := (DispatchSpecWalkCR32.raise e1).run s hcode hRun (by rw [hr]; exact hnt)
    rw [hr] at h1
    refine ⟨?_, fun _ => h1.2 (by simp)⟩
    intro h; cases h

private theorem return_const0_chainPostR32 {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {v : ValueHOL 64}
    (hpost : OpDispatchChainPostR32 (callEntryStateHOLFinite s callee) (some (.returned v)) cpost) :
    OpDispatchChainPostR32 s
      (evaluateHOLFiniteState { cpost with locals := s.locals } (.return (.const 0))).1
      (evaluateHOLFiniteState { cpost with locals := s.locals } (.return (.const 0))).2 := by
  rw [evaluateHOLFiniteState_return]
  have hc0 : @evalHOLExact 64 F _ ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).toExact
      (fun a => Classical.propDecidable (cpost.memaddrs a)) (.const 0) =
      some (.val (.word 0)) := rfl
  rw [hc0]; dsimp only
  have hsz : sizeOfShapeWithContextHOL cpost.structs
      (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
    simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
  rw [if_pos hsz]; dsimp only
  obtain ⟨⟨hInv_cp, hWF_cp⟩, hPot_cp⟩ := hpost.1 ⟨v, rfl⟩
  have hcongr_ce := evm_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl
  have hcongr_ret := evm_congr (s := cpost)
    (t := emptyLocalsHOLFinite { cpost with locals := s.locals }) rfl rfl
  have hInv_ret : EvmInvR32 (emptyLocalsHOLFinite { cpost with locals := s.locals }) :=
    localsFree_evmInvR32 cpost _ cpost.clock hInv_cp
  have hWF_ret : HeadMemBridge.HeadMemChainWF (emptyLocalsHOLFinite { cpost with locals := s.locals }) :=
    (HeadMemBridge.headMemChainWF_congr
      (s := cpost) (t := emptyLocalsHOLFinite { cpost with locals := s.locals }) rfl rfl).mpr hWF_cp
  refine ⟨fun _ => ⟨⟨hInv_ret, hWF_ret⟩, by rw [hcongr_ret.1, ← hcongr_ce.1]; exact hPot_cp⟩, ?_⟩
  rintro ⟨_, h⟩; cases h

private theorem call_exception_chainPostR32 {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {eid : MlS} {ev : ValueHOL 64}
    (hQ : OpDispatchChainPostR32 (callEntryStateHOLFinite s callee) (some (.exception eid ev)) cpost) :
    OpDispatchChainPostR32 s (some (.exception eid ev)) cpost.emptyLocalsHOLFinite := by
  by_cases heid : eid = ofString "EvmErr"
  · subst heid
    exact opDispatchChainPostR32_congr_lc (s := s) (s' := callEntryStateHOLFinite s callee)
      (post := cpost) (post' := cpost.emptyLocalsHOLFinite) rfl rfl rfl rfl rfl hQ
  · refine opDispatchChainPostR32_other (by intro _ h; cases h) ?_
    rintro ⟨_, h⟩
    injection h with h'; injection h' with h1 _; exact heid h1

private theorem evmChainRunR32_callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (h : EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) :
    EvmInvR32 (callEntryStateHOLFinite s callee) ∧
    HeadMemBridge.HeadMemChainWF (callEntryStateHOLFinite s callee) ∧
    ¬ EvmDone (callEntryStateHOLFinite s callee) := by
  have hrun := evmRun_callEntry s callee ⟨h.1.1, h.2.2⟩
  have hwf : HeadMemBridge.HeadMemChainWF (callEntryStateHOLFinite s callee) :=
    (HeadMemBridge.headMemChainWF_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl).mpr h.2.1
  exact ⟨⟨hrun.1, StorageCreateFinish.witnessDbOK_with_locals_clock h.1.2.1 callee (s.clock - 1),
    h.1.2.2⟩, hwf, hrun.2⟩

theorem DispatchSpecWalkCR32.callReturn {fname : MlS}
    (hf : OpHandlerChainSpecR32 fname) (args : List (ExpHOL 64)) :
    DispatchSpecWalkCR32 (.seq (.call (some (none, none)) fname args) (.return (.const 0))) := by
  refine ⟨fun {F} s hcode hRun hnt => ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩⟩
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact opDispatchChainPostR32_error s s
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchChainPostR32_error s s
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hce_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hcode
        have hce_run := evmChainRunR32_callEntry s callee hRun
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
        simp only [hrun] at hnt ⊢
        have hQ (hsafe : res ≠ some .timeOut) :
            OpDispatchChainPostR32 (callEntryStateHOLFinite s callee) res cpost := by
          have hbody : body' = body :=
            lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
              retShape ret' values callee (by rw [hcode]; exact hlook) hl
          subst body'
          have hce_ex : ∃ vals, lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
              some (body, (callEntryStateHOLFinite s callee).locals, retShape) := by
            refine ⟨values, ?_⟩
            rw [← hcode] at hlook ⊢
            have hret : ret' = retShape := by
              have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
                s.code.lookup fname values body callee ret' hl
              simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
              split at hx
              · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
              · cases hx
            subst hret; exact hl
          have hsp := hspec (callEntryStateHOLFinite s callee) hce_code hce_run hce_ex (by rw [hrun]; exact hsafe)
          rw [hrun] at hsp; exact hsp
        cases res with
        | none => exact opDispatchChainPostR32_error s cpost
        | some r0 =>
          cases r0 with
          | returned v =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte]
              exact return_const0_chainPostR32 (hQ (by simp))
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchChainPostR32_error s cpost
          | timeOut => simp at hnt
          | exception eid ev => exact call_exception_chainPostR32 (hQ (by simp))
          | «break» => exact opDispatchChainPostR32_error s cpost
          | «continue» => exact opDispatchChainPostR32_error s cpost
          | finalFfi f =>
            refine opDispatchChainPostR32_other (s := s) (t := cpost.emptyLocalsHOLFinite)
              (r := some (.finalFfi f)) (by intro _ h; cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchChainPostR32_error s cpost.emptyLocalsHOLFinite

theorem DispatchSpecWalkCR32.seq {p q : ProgHOL 64}
    (h1 : DispatchSpecWalkCR32 p) (h2 : DispatchSpecWalkCR32 q) :
    DispatchSpecWalkCR32 (.seq p q) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr1 : evaluateHOLFiniteState s p with ⟨r1, mid⟩
  simp only [hr1] at hnt ⊢
  cases r1 with
  | none =>
    have hp := h1.run s hcode hRun (by rw [hr1]; simp)
    rw [hr1] at hp
    have hmid : mid = s := hp.1 rfl
    subst mid
    exact h2.run s hcode hRun hnt
  | some _ =>
    have hp := h1.run s hcode hRun (by rw [hr1]; exact hnt)
    rw [hr1] at hp
    refine ⟨?_, fun _ => hp.2 (by simp)⟩
    intro h; cases h

theorem DispatchSpecWalkCR32.ite (c : ExpHOL 64) {p q : ProgHOL 64}
    (h1 : DispatchSpecWalkCR32 p) (h2 : DispatchSpecWalkCR32 q) :
    DispatchSpecWalkCR32 (.ite c p q) := by
  refine ⟨fun {F} s hcode hRun hnt => ?_⟩
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w _
    by_cases hw : w = 0
    · simp only [hw, ↓reduceIte]
      intro hnt; exact h2.run s hcode hRun hnt
    · simp only [hw, ↓reduceIte]
      intro hnt; exact h1.run s hcode hRun hnt
  · intro _
    refine ⟨?_, fun _ => opDispatchChainPostR32_error s s⟩
    intro h; cases h

private theorem callReturnC_one_word_boundedR32
    {fname paramName : MlS} {bound : Nat} {argExp : ExpHOL 64}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hf : FunSpec
      (fun s => (EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) ∧
        ∃ w : BitVec 64, s.locals.lookup paramName = some (.val (.word w)) ∧ w.toNat ≤ bound)
      OpDispatchChainPostR32 fname)
    (hlk_param : ∃ fbody, originalRuntimeCode.lookup fname = some ([(paramName, .one)], fbody, .one))
    (harg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∃ w : BitVec 64,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] =
          some [.val (.word w)] ∧
        w.toNat ≤ bound) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode →
      (EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) → P s →
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).1 ≠
        some .timeOut →
      OpDispatchChainPostR32 s
        (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).1
        (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).2 := by
  intro F s hcode hRun hPs hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  obtain ⟨fbody, hlk_exact⟩ := hlk_param
  obtain ⟨argw, harg_ev, harg_le⟩ := harg s hPs
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rw [harg_ev] at hnt ⊢; dsimp only at hnt ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname [.val (.word argw)] with _ | ⟨body', callee, ret'⟩
  · exact opDispatchChainPostR32_error s s
  · simp only [hl] at hnt ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · simp only [hz, ↓reduceIte] at hnt ⊢
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname [.val (.word argw)] =
          some (body', callee, ret') := by rwa [← hcode]
      obtain ⟨_, hret1, w', hw_eq, hcal_lk⟩ :=
        R14Shards.OpHandlersA.one_word_arg_lookup hlk_exact hl_orig
      injection hw_eq with hw1; injection hw1 with hw2; subst hw2
      have hce_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hcode
      have hce_pre : (EvmInvR32 (callEntryStateHOLFinite s callee) ∧
          HeadMemBridge.HeadMemChainWF (callEntryStateHOLFinite s callee) ∧
          ¬ EvmDone (callEntryStateHOLFinite s callee)) ∧
          ∃ w : BitVec 64, (callEntryStateHOLFinite s callee).locals.lookup paramName =
            some (.val (.word w)) ∧ w.toNat ≤ bound :=
        ⟨evmChainRunR32_callEntry s callee hRun, argw, hcal_lk, harg_le⟩
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
      simp only [hrun] at hnt ⊢
      have hQ (hsafe : res ≠ some .timeOut) :
          OpDispatchChainPostR32 (callEntryStateHOLFinite s callee) res cpost := by
        have hbody : body' = body :=
          lookupCodeHOLFinite_installed_body s.code.lookup fname params body body'
            retShape ret' [.val (.word argw)] callee (by rw [hcode]; exact hlook) hl
        have hret : ret' = retShape := by
          have hlk_eq : some ([(paramName, ShapeHOL.one)], fbody, ShapeHOL.one) =
              some (params, body, retShape) := hlk_exact.symm.trans hlook
          injection hlk_eq with hp1
          rcases Prod.mk.inj hp1 with ⟨_, hp2⟩
          exact hret1.trans (Prod.mk.inj hp2).2
        have hce_ex : ∃ vals, lookupCodeHOLFinite originalRuntimeCode.lookup fname vals =
            some (body, (callEntryStateHOLFinite s callee).locals, retShape) := by
          refine ⟨[.val (.word argw)], ?_⟩
          rwa [← hbody, ← hret]
        have hrun_b : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (res, cpost) := by
          rwa [← hbody]
        have hsp := hspec (callEntryStateHOLFinite s callee) hce_code hce_pre hce_ex
          (by rw [hrun_b]; exact hsafe)
        rw [hrun_b] at hsp; exact hsp
      cases res with
      | none => exact opDispatchChainPostR32_error s cpost
      | some r0 =>
        cases r0 with
        | returned v =>
          by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
          · simp only [hsh, ↓reduceIte]
            exact return_const0_chainPostR32 (hQ (by simp))
          · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
            exact opDispatchChainPostR32_error s cpost
        | timeOut => simp at hnt
        | exception eid ev => exact call_exception_chainPostR32 (hQ (by simp))
        | «break» => exact opDispatchChainPostR32_error s cpost
        | «continue» => exact opDispatchChainPostR32_error s cpost
        | finalFfi f =>
          refine opDispatchChainPostR32_other (s := s) (t := cpost.emptyLocalsHOLFinite)
            (r := some (.finalFfi f)) (by intro _ h; cases h) ?_
          rintro ⟨_, h⟩; cases h
        | error => exact opDispatchChainPostR32_error s cpost.emptyLocalsHOLFinite

/-! ## 4. The 87-field R32 cutover handler bundle -/

/-- Complete R32 opcode handler bundle for `OpDispatchSpecAR32` with range-bounded
`op_push` (`n ≤ 32`) and `op_log` (`ntopics ≤ 4`). -/
structure OpDispatchChainHandlersCutoverR32 : Prop where
  op_stop : OpHandlerChainSpecR32 (ofString "op_stop")
  op_add : OpHandlerChainSpecR32 (ofString "op_add")
  op_mul : OpHandlerChainSpecR32 (ofString "op_mul")
  op_sub : OpHandlerChainSpecR32 (ofString "op_sub")
  op_div : OpHandlerChainSpecR32 (ofString "op_div")
  op_sdiv : OpHandlerChainSpecR32 (ofString "op_sdiv")
  op_mod : OpHandlerChainSpecR32 (ofString "op_mod")
  op_smod : OpHandlerChainSpecR32 (ofString "op_smod")
  op_addmod : OpHandlerChainSpecR32 (ofString "op_addmod")
  op_mulmod : OpHandlerChainSpecR32 (ofString "op_mulmod")
  op_exp : OpHandlerChainSpecR32 (ofString "op_exp")
  op_signextend : OpHandlerChainSpecR32 (ofString "op_signextend")
  op_lt : OpHandlerChainSpecR32 (ofString "op_lt")
  op_gt : OpHandlerChainSpecR32 (ofString "op_gt")
  op_slt : OpHandlerChainSpecR32 (ofString "op_slt")
  op_sgt : OpHandlerChainSpecR32 (ofString "op_sgt")
  op_eq : OpHandlerChainSpecR32 (ofString "op_eq")
  op_iszero : OpHandlerChainSpecR32 (ofString "op_iszero")
  op_and : OpHandlerChainSpecR32 (ofString "op_and")
  op_or : OpHandlerChainSpecR32 (ofString "op_or")
  op_xor : OpHandlerChainSpecR32 (ofString "op_xor")
  op_not : OpHandlerChainSpecR32 (ofString "op_not")
  op_byte : OpHandlerChainSpecR32 (ofString "op_byte")
  op_shl : OpHandlerChainSpecR32 (ofString "op_shl")
  op_shr : OpHandlerChainSpecR32 (ofString "op_shr")
  op_sar : OpHandlerChainSpecR32 (ofString "op_sar")
  op_clz : OpHandlerChainSpecR32 (ofString "op_clz")
  op_keccak : OpHandlerChainSpecR32 (ofString "op_keccak")
  op_address : OpHandlerChainSpecR32 (ofString "op_address")
  op_balance : OpHandlerChainSpecR32 (ofString "op_balance")
  op_origin : OpHandlerChainSpecR32 (ofString "op_origin")
  op_caller : OpHandlerChainSpecR32 (ofString "op_caller")
  op_callvalue : OpHandlerChainSpecR32 (ofString "op_callvalue")
  op_calldataload : OpHandlerChainSpecR32 (ofString "op_calldataload")
  op_calldatasize : OpHandlerChainSpecR32 (ofString "op_calldatasize")
  op_calldatacopy : OpHandlerChainSpecR32 (ofString "op_calldatacopy")
  op_codesize : OpHandlerChainSpecR32 (ofString "op_codesize")
  op_codecopy : OpHandlerChainSpecR32 (ofString "op_codecopy")
  op_gasprice : OpHandlerChainSpecR32 (ofString "op_gasprice")
  op_extcodesize : OpHandlerChainSpecR32 (ofString "op_extcodesize")
  op_extcodecopy : OpHandlerChainSpecR32 (ofString "op_extcodecopy")
  op_returndatasize : OpHandlerChainSpecR32 (ofString "op_returndatasize")
  op_returndatacopy : OpHandlerChainSpecR32 (ofString "op_returndatacopy")
  op_extcodehash : OpHandlerChainSpecR32 (ofString "op_extcodehash")
  op_blockhash : OpHandlerChainSpecR32 (ofString "op_blockhash")
  op_coinbase : OpHandlerChainSpecR32 (ofString "op_coinbase")
  op_timestamp : OpHandlerChainSpecR32 (ofString "op_timestamp")
  op_number : OpHandlerChainSpecR32 (ofString "op_number")
  op_prevrandao : OpHandlerChainSpecR32 (ofString "op_prevrandao")
  op_gaslimit : OpHandlerChainSpecR32 (ofString "op_gaslimit")
  op_chainid : OpHandlerChainSpecR32 (ofString "op_chainid")
  op_selfbalance : OpHandlerChainSpecR32 (ofString "op_selfbalance")
  op_basefee : OpHandlerChainSpecR32 (ofString "op_basefee")
  op_blobhash : OpHandlerChainSpecR32 (ofString "op_blobhash")
  op_blobbasefee : OpHandlerChainSpecR32 (ofString "op_blobbasefee")
  op_slotnum : OpHandlerChainSpecR32 (ofString "op_slotnum")
  op_pop : OpHandlerChainSpecR32 (ofString "op_pop")
  op_mload : OpHandlerChainSpecR32 (ofString "op_mload")
  op_mstore : OpHandlerChainSpecR32 (ofString "op_mstore")
  op_mstore8 : OpHandlerChainSpecR32 (ofString "op_mstore8")
  op_sload : OpHandlerChainSpecR32 (ofString "op_sload")
  op_sstore : OpHandlerChainSpecR32 (ofString "op_sstore")
  op_jump : OpHandlerChainSpecR32 (ofString "op_jump")
  op_jumpi : OpHandlerChainSpecR32 (ofString "op_jumpi")
  op_pc : OpHandlerChainSpecR32 (ofString "op_pc")
  op_msize : OpHandlerChainSpecR32 (ofString "op_msize")
  op_gas : OpHandlerChainSpecR32 (ofString "op_gas")
  op_jumpdest : OpHandlerChainSpecR32 (ofString "op_jumpdest")
  op_tload : OpHandlerChainSpecR32 (ofString "op_tload")
  op_tstore : OpHandlerChainSpecR32 (ofString "op_tstore")
  op_mcopy : OpHandlerChainSpecR32 (ofString "op_mcopy")
  op_push : OpPushBoundedChainSpecR32
  op_dup : OpHandlerChainSpecR32 (ofString "op_dup")
  op_swap : OpHandlerChainSpecR32 (ofString "op_swap")
  op_log : OpLogBoundedChainSpecR32
  op_dupn : OpHandlerChainSpecR32 (ofString "op_dupn")
  op_swapn : OpHandlerChainSpecR32 (ofString "op_swapn")
  op_exchange : OpHandlerChainSpecR32 (ofString "op_exchange")
  op_create : OpHandlerChainSpecR32 (ofString "op_create")
  op_call : OpHandlerChainSpecR32 (ofString "op_call")
  op_callcode : OpHandlerChainSpecR32 (ofString "op_callcode")
  op_return : OpHandlerChainSpecR32 (ofString "op_return")
  op_delegatecall : OpHandlerChainSpecR32 (ofString "op_delegatecall")
  op_create2 : OpHandlerChainSpecR32 (ofString "op_create2")
  op_staticcall : OpHandlerChainSpecR32 (ofString "op_staticcall")
  op_revert : OpHandlerChainSpecR32 (ofString "op_revert")
  op_selfdestruct : OpHandlerChainSpecR32 (ofString "op_selfdestruct")

/-! ## 5. The R32 walk lemmas -/

private theorem push0_walkCR32 (h_push : OpPushBoundedChainSpecR32) :
    DispatchSpecWalkCR32 (.seq (.call (some (none, none)) (ofString "op_push") [.const 0#64]) (.return (.const 0))) := by
  refine ⟨fun {F} s hcode hRun hnt => ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩⟩
  exact callReturnC_one_word_boundedR32 (P := fun _ => True) h_push ⟨_, lookup_op_push⟩
    (fun _ _ => ⟨0#64, rfl, by decide⟩) s hcode hRun trivial hnt

private theorem ite_push_sub95_walkCR32
    (h_op_push : OpPushBoundedChainSpecR32)
    {F : Type} (s : PanSemStateFiniteExact 64 F) {opw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hRun : EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
    (hop : s.locals.lookup (ofString "op") = some (.val (.word opw)))
    (hlo : 96 ≤ opw.toNat)
    {p_push : ProgHOL 64}
    (hp_eq : p_push = .ite (.cmp .lower (.var .local (ofString "op")) (.const 128#64))
      (.seq (.call (some (none, none)) (ofString "op_push")
        [.op .sub [.var .local (ofString "op"), .const 95#64]]) (.return (.const 0)))
      .skip)
    (hnt : (evaluateHOLFiniteState s p_push).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s p_push).1 = none →
      (evaluateHOLFiniteState s p_push).2 = s) ∧
    ((evaluateHOLFiniteState s p_push).1 ≠ none →
      OpDispatchChainPostR32 s (evaluateHOLFiniteState s p_push).1 (evaluateHOLFiniteState s p_push).2) := by
  subst hp_eq
  rw [evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hlt : opw < 128#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hnt ⊢
    have hhi : opw.toNat < 128 := by simpa [BitVec.lt_def] using hlt
    refine ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩
    exact callReturnC_one_word_boundedR32
      (P := fun t => t.locals.lookup (ofString "op") = some (.val (.word opw)))
      h_op_push ⟨_, lookup_op_push⟩
      (fun t htop => ⟨opw - 95#64, evalList_sub_op_const t htop, push_arg_sub95_le_32 hlo hhi⟩)
      s hcode hRun hop hnt
  · simp only [hlt, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

private theorem ite_log_sub160_walkCR32
    (h_op_log : OpLogBoundedChainSpecR32)
    {F : Type} (s : PanSemStateFiniteExact 64 F) {opw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hRun : EvmInvR32 s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
    (hop : s.locals.lookup (ofString "op") = some (.val (.word opw)))
    (hlo : 160 ≤ opw.toNat)
    {p_log : ProgHOL 64}
    (hp_eq : p_log = .ite (.cmp .lower (.var .local (ofString "op")) (.const 165#64))
      (.seq (.call (some (none, none)) (ofString "op_log")
        [.op .sub [.var .local (ofString "op"), .const 160#64]]) (.return (.const 0)))
      .skip)
    (hnt : (evaluateHOLFiniteState s p_log).1 ≠ some .timeOut) :
    ((evaluateHOLFiniteState s p_log).1 = none →
      (evaluateHOLFiniteState s p_log).2 = s) ∧
    ((evaluateHOLFiniteState s p_log).1 ≠ none →
      OpDispatchChainPostR32 s (evaluateHOLFiniteState s p_log).1 (evaluateHOLFiniteState s p_log).2) := by
  subst hp_eq
  rw [evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hlt : opw < 165#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hnt ⊢
    have hhi : opw.toNat < 165 := by simpa [BitVec.lt_def] using hlt
    refine ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩
    exact callReturnC_one_word_boundedR32
      (P := fun t => t.locals.lookup (ofString "op") = some (.val (.word opw)))
      h_op_log ⟨_, lookup_op_log_cutover⟩
      (fun t htop => ⟨opw - 160#64, evalList_sub_op_const t htop, log_arg_sub160_le_4 hlo hhi⟩)
      s hcode hRun hop hnt
  · simp only [hlt, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

private theorem walkCR32_group01 (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 dispatchGroup01 :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_stop _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_add _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_mul _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_sub _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_div _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_sdiv _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_mod _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_smod _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_addmod _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_mulmod _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_exp _) DispatchSpecWalkCR32.skip)
    (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_signextend _) DispatchSpecWalkCR32.skip)))))))))))

private theorem walkCR32_group02 (h : OpDispatchChainHandlersCutoverR32)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkCR32 tail) :
    DispatchSpecWalkCR32 (dispatchGroup02 tail) :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_lt _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_gt _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_slt _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_sgt _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_eq _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_iszero _) DispatchSpecWalkCR32.skip)
    ht)))))

private theorem walkCR32_group03 (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 dispatchGroup03 :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_and _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_or _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_xor _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_not _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_byte _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_shl _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_shr _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_sar _) DispatchSpecWalkCR32.skip)
    (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_clz _) DispatchSpecWalkCR32.skip))))))))

private theorem walkCR32_group04 (h : OpDispatchChainHandlersCutoverR32)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkCR32 tail) :
    DispatchSpecWalkCR32 (dispatchGroup04 tail) :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_keccak _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_address _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_balance _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_origin _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_caller _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_callvalue _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_calldataload _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_calldatasize _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_calldatacopy _) DispatchSpecWalkCR32.skip)
    ht))))))))

private theorem walkCR32_group05 (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 dispatchGroup05 :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_codesize _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_codecopy _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_gasprice _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_extcodesize _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_extcodecopy _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_returndatasize _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_returndatacopy _) DispatchSpecWalkCR32.skip)
    (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_extcodehash _) DispatchSpecWalkCR32.skip)))))))

private theorem walkCR32_group06 (h : OpDispatchChainHandlersCutoverR32)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkCR32 tail) :
    DispatchSpecWalkCR32 (dispatchGroup06 tail) :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_blockhash _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_coinbase _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_timestamp _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_number _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_prevrandao _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_gaslimit _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_chainid _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_selfbalance _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_basefee _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_blobhash _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_blobbasefee _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_slotnum _) DispatchSpecWalkCR32.skip)
    ht)))))))))))

private theorem walkCR32_group07 (h : OpDispatchChainHandlersCutoverR32)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkCR32 tail) :
    DispatchSpecWalkCR32 (dispatchGroup07 tail) :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_pop _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_mload _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_mstore _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_mstore8 _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_sload _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_sstore _) DispatchSpecWalkCR32.skip)
    ht)))))

private theorem walkCR32_group08 (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 dispatchGroup08 :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_jump _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_jumpi _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_pc _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_msize _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_gas _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_jumpdest _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_tload _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_tstore _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_mcopy _) DispatchSpecWalkCR32.skip)
    (DispatchSpecWalkCR32.ite _ (push0_walkCR32 h.op_push) DispatchSpecWalkCR32.skip)))))))))

private theorem walkCR32_group11 (h : OpDispatchChainHandlersCutoverR32)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkCR32 tail) :
    DispatchSpecWalkCR32 (dispatchGroup11 tail) :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_create _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_call _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_callcode _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_return _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_delegatecall _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_create2 _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_staticcall _) DispatchSpecWalkCR32.skip)
    ht))))))

private theorem walkCR32_group12 (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 dispatchGroup12 :=
  DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_revert _) DispatchSpecWalkCR32.skip)
  (DispatchSpecWalkCR32.seq (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_selfdestruct _) DispatchSpecWalkCR32.skip)
    (DispatchSpecWalkCR32.seqRaiseReturn _ _))

private theorem walkCR32_group01_to_03 (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 (binaryAt [0] dispatchCode) :=
  DispatchSpecWalkCR32.ite _
    (DispatchSpecWalkCR32.seq
      (DispatchSpecWalkCR32.ite _ (walkCR32_group01 h) (walkCR32_group02 h (walkCR32_group03 h)))
      (DispatchSpecWalkCR32.raise _))
    DispatchSpecWalkCR32.skip

private theorem walkCR32_group04_to_08 (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 (binaryAt [1, 0] dispatchCode) :=
  DispatchSpecWalkCR32.ite _
    (DispatchSpecWalkCR32.seq
      (DispatchSpecWalkCR32.ite _
        (walkCR32_group04 h (walkCR32_group05 h))
        (walkCR32_group06 h (walkCR32_group07 h (walkCR32_group08 h))))
      (DispatchSpecWalkCR32.raise _))
    DispatchSpecWalkCR32.skip

private theorem walkCR32_dup_swap (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 (binaryAt [1, 1, 0, 0, 1] dispatchCode) :=
  DispatchSpecWalkCR32.seq
    (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_dup _) DispatchSpecWalkCR32.skip)
    (DispatchSpecWalkCR32.callReturn h.op_swap _)

private theorem walkCR32_after_log (h : OpDispatchChainHandlersCutoverR32) :
    DispatchSpecWalkCR32 (binaryAt [1, 1, 1, 1] dispatchCode) :=
  DispatchSpecWalkCR32.seq
    (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_dupn _) DispatchSpecWalkCR32.skip)
    (DispatchSpecWalkCR32.seq
      (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_swapn _) DispatchSpecWalkCR32.skip)
      (DispatchSpecWalkCR32.seq
        (DispatchSpecWalkCR32.ite _ (DispatchSpecWalkCR32.callReturn h.op_exchange _) DispatchSpecWalkCR32.skip)
        (walkCR32_group11 h (walkCR32_group12 h))))

/-- Chain-WF R32 `op_dispatch` theorem: reduces `OpDispatchSpecAR32` to
`OpDispatchChainHandlersCutoverR32` (with bounded `op_push` `n ≤ 32` and bounded
`op_log` `ntopics ≤ 4`). -/
theorem op_dispatch_chain_spec_cutover_r32
    (h : OpDispatchChainHandlersCutoverR32) :
    OpDispatchSpecAR32 := by
  have hlk_disp : originalRuntimeCode.lookup (ofString "op_dispatch") =
      some ([(ofString "op", .one)], dispatchCode, .one) := lookup_op_dispatch
  refine ⟨_, _, _, hlk_disp, ?_⟩
  intro F s hcode hRun hex hnt
  obtain ⟨opw, hop⟩ := op_dispatch_param_word hex
  change OpDispatchChainPostR32 s (evaluateHOLFiniteState s dispatchCode).1 (evaluateHOLFiniteState s dispatchCode).2
  let p0 := binaryAt [0] dispatchCode
  let p1 := binaryAt [1, 0] dispatchCode
  let p2 := binaryAt [1, 1, 0] dispatchCode
  let p3 := binaryAt [1, 1, 1, 0] dispatchCode
  let p4 := binaryAt [1, 1, 1, 1] dispatchCode
  have hspine : dispatchCode = .seq p0 (.seq p1 (.seq p2 (.seq p3 p4))) := rfl
  rw [hspine] at hnt ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hr0 : evaluateHOLFiniteState s p0 with ⟨r0, s1⟩
  simp only [hr0] at hnt ⊢
  cases r0 with
  | some _ =>
    have hw0 := (walkCR32_group01_to_03 h).run s hcode hRun (by rw [hr0]; exact hnt)
    rw [hr0] at hw0
    exact hw0.2 (by simp)
  | none =>
    have hs1 : s = s1 := by
      have hw0 := (walkCR32_group01_to_03 h).run s hcode hRun (by rw [hr0]; simp)
      rw [hr0] at hw0; exact (hw0.1 rfl).symm
    subst hs1
    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s2⟩
    simp only [hr1] at hnt ⊢
    cases r1 with
    | some _ =>
      have hw1 := (walkCR32_group04_to_08 h).run s hcode hRun (by rw [hr1]; exact hnt)
      rw [hr1] at hw1
      exact hw1.2 (by simp)
    | none =>
      have hp1_shape : p1 = .ite (.cmp .lower (.var .local (ofString "op")) (.const 96#64))
          (.seq (binaryAt [1, 0, 0, 0] dispatchCode) (.raise (ofString "EvmErr") (.const 5)))
          .skip := rfl
      have hge96_pair : s2 = s ∧ 96 ≤ opw.toNat := by
        have h96 := ite_then_never_none_skip (k := 96#64) s hop
          (fun t => seq_raise_never_none t _ (ofString "EvmErr") (.const 5))
          (by rw [← hp1_shape, hr1])
        rwa [← hp1_shape, hr1] at h96
      obtain ⟨hs2, hge96⟩ := hge96_pair
      have hs2' : s = s2 := hs2.symm
      subst hs2'
      rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
      rcases hr2 : evaluateHOLFiniteState s p2 with ⟨r2, s3⟩
      simp only [hr2] at hnt ⊢
      let p2_push := binaryAt [1, 1, 0, 0, 0] dispatchCode
      let p2_ds := binaryAt [1, 1, 0, 0, 1] dispatchCode
      have hp2_shape : p2 = .ite (.cmp .lower (.var .local (ofString "op")) (.const 160#64))
          (.seq p2_push p2_ds) .skip := rfl
      cases r2 with
      | some _ =>
        have hnt2 : (evaluateHOLFiniteState s p2).1 ≠ some .timeOut := by rw [hr2]; exact hnt
        have hgoal : OpDispatchChainPostR32 s (evaluateHOLFiniteState s p2).1 (evaluateHOLFiniteState s p2).2 := by
          rw [hp2_shape, evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt2 hr2 ⊢
          dsimp only at hnt2 hr2 ⊢
          by_cases hlt160 : opw < 160#64
          · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
            simp only [hlt160, ↓reduceIte, h10] at hnt2 hr2 ⊢
            rw [evaluateHOLFiniteState_seq_line780] at hnt2 hr2 ⊢
            rcases hpush : evaluateHOLFiniteState s p2_push with ⟨rp, sp⟩
            simp only [hpush] at hnt2 hr2 ⊢
            cases rp with
            | some _ =>
              have hp := ite_push_sub95_walkCR32 (p_push := p2_push)
                h.op_push s hcode hRun hop hge96 rfl
                (by rw [hpush]; exact hnt2)
              rw [hpush] at hp
              exact hp.2 (by simp)
            | none =>
              have hp := ite_push_sub95_walkCR32 (p_push := p2_push)
                h.op_push s hcode hRun hop hge96 rfl
                (by rw [hpush]; simp)
              rw [hpush] at hp
              have hsp : s = sp := (hp.1 rfl).symm
              subst hsp
              dsimp only at hnt2 hr2 ⊢
              have hds := (walkCR32_dup_swap h).run s hcode hRun hnt2
              exact hds.2 (by rw [hr2]; simp)
          · simp only [hlt160, ↓reduceIte] at hr2
            rw [evaluateHOLFiniteState_skip] at hr2
            cases hr2
        rwa [hr2] at hgoal
      | none =>
        have hp2_body_shape : ProgHOL.seq p2_push p2_ds =
            ProgHOL.seq p2_push (.seq (binaryAt [1, 1, 0, 0, 1, 0] dispatchCode)
              (.seq (.call (some (none, none)) (ofString "op_swap")
                [.op .sub [.var .local (ofString "op"), .const 143#64]]) (.return (.const 0)))) := rfl
        have hge160_pair : s3 = s ∧ 160 ≤ opw.toNat := by
          have h160 := ite_then_never_none_skip (k := 160#64) (thenBr := ProgHOL.seq p2_push p2_ds) s hop
            (fun t => by rw [hp2_body_shape]; exact body578_302_never_none t _ _ _ (.const 0))
            (by rw [← hp2_shape, hr2])
          rwa [← hp2_shape, hr2] at h160
        obtain ⟨hs3, hge160⟩ := hge160_pair
        have hs3' : s = s3 := hs3.symm
        subst hs3'
        rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hr3 : evaluateHOLFiniteState s p3 with ⟨r3, s4⟩
        simp only [hr3] at hnt ⊢
        cases r3 with
        | some _ =>
          have hlogw := ite_log_sub160_walkCR32 (p_log := p3) h.op_log s hcode hRun hop hge160 rfl
            (by rw [hr3]; exact hnt)
          rw [hr3] at hlogw
          exact hlogw.2 (by simp)
        | none =>
          have hlogw := ite_log_sub160_walkCR32 (p_log := p3) h.op_log s hcode hRun hop hge160 rfl
            (by rw [hr3]; simp)
          rw [hr3] at hlogw
          have hs4 : s = s4 := (hlogw.1 rfl).symm
          subst hs4
          dsimp only at hnt ⊢
          rcases hr4 : evaluateHOLFiniteState s p4 with ⟨r4, s5⟩
          cases r4 with
          | none =>
            exact opDispatchChainPostR32_other (by intro _ hv; cases hv) (by rintro ⟨_, hv⟩; cases hv)
          | some _ =>
            have hw4 := (walkCR32_after_log h).run s hcode hRun hnt
            rw [hr4] at hw4
            exact hw4.2 (by simp)

end InitECandidate.Solver.Wave8GuestInv.ContractParts
