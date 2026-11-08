import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterCutover
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge

/-! # Chain-WF Cutover `op_dispatch` Router (`HeadMemBridge.OpDispatchSpecA`)

Range-aware `HeadMemBridge.HeadMemChainWF`-preserving `op_dispatch` router:
- Uses `dispatchCode`'s `op` lower-bound spine (`0 -> 32 -> 96 -> 160`) so that:
  - `op == 95` calls `op_push [0#64]` with `nbytes = 0#64` (`0 ≤ 32`),
  - `96 ≤ op < 128` calls `op_push [op - 95#64]` with `nbytes.toNat ≤ 32`,
  - `160 ≤ op < 165` calls `op_log [op - 160#64]` with `ntopics.toNat ≤ 4`.
- Reduces `HeadMemBridge.OpDispatchSpecA` cleanly to `OpDispatchChainHandlersCutover`,
  allowing `StrongBridges` to plug in all already-proved chain-WF opcode specs
  (`op_return_chainSpecA`, `op_revert_chainSpecA`, `op_mcopy_chainSpecA`,
  `op_selfdestruct_chainSpecA`, `op_create_chainSpecA`, `op_create2_chainSpecA`,
  `op_delegatecall_chainSpecA`).
-/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterAligned
open InitECandidate.Solver.Wave8Contracts.M23

/-- Postcondition of `HeadMemBridge.OpDispatchSpecA` on initial state `s`. -/
def OpDispatchChainPost {F : Type} (s : PanSemStateFiniteExact 64 F)
    (r : Option (PanSemResultExact 64)) (post : PanSemStateFiniteExact 64 F) : Prop :=
  ((∃ v, r = some (.returned v)) →
    (EvmInv post ∧ HeadMemBridge.HeadMemChainWF post) ∧ evmPot post < evmPot s) ∧
  (IsEvmErr r →
    (EvmInv post ∧ HeadMemBridge.HeadMemChainWF post) ∧
      (evmChain post).length = (evmChain s).length ∧
      Wave8GuestInv.evmR post ≤ Wave8GuestInv.evmR s)

/-- Opcode handler spec carrying `HeadMemBridge.HeadMemChainWF` (identical to
`StrongBridges.OpHandlerChainSpecA`). -/
def OpHandlerChainSpec (fname : MlS) : Prop :=
  FunSpec (fun s => EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
    OpDispatchChainPost fname

/-- Bounded `op_push` (`nbytes ≤ 32`) carrying `HeadMemBridge.HeadMemChainWF`. -/
def OpPushBoundedChainSpec : Prop :=
  FunSpec
    (fun s => (EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nbytes") = some (.val (.word n)) ∧ n.toNat ≤ 32)
    OpDispatchChainPost
    (ofString "op_push")

/-- Bounded `op_log` (`ntopics ≤ 4`) carrying `HeadMemBridge.HeadMemChainWF`. -/
def OpLogBoundedChainSpec : Prop :=
  FunSpec
    (fun s => (EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) ∧
      ∃ nt : BitVec 64, s.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧ nt.toNat ≤ 4)
    OpDispatchChainPost
    (ofString "op_log")

theorem opDispatchChainPost_other {F : Type} {s t : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hnret : ∀ v, r ≠ some (.returned v)) (hnerr : ¬ IsEvmErr r) :
    OpDispatchChainPost s r t :=
  ⟨fun ⟨v, hv⟩ => (hnret v hv).elim, fun he => (hnerr he).elim⟩

theorem opDispatchChainPost_error {F : Type} (s t : PanSemStateFiniteExact 64 F) :
    OpDispatchChainPost s (some .error) t :=
  opDispatchChainPost_other (by intro _ h; cases h) (by rintro ⟨_, h⟩; cases h)

theorem opDispatchChainPost_congr_lc {F : Type} {s s' post post' : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hs_m : s'.memory = s.memory) (hs_g : s'.globals = s.globals)
    (hp_m : post'.memory = post.memory) (hp_g : post'.globals = post.globals)
    (hp_lc : post' = { post with locals := post'.locals, clock := post'.clock })
    (h : OpDispatchChainPost s' r post) :
    OpDispatchChainPost s r post' := by
  have hcs := evm_congr hs_m hs_g
  have hcp := evm_congr hp_m hp_g
  have hInv (hi : EvmInv post) : EvmInv post' := by
    rw [hp_lc]; exact localsFree_evmInv post _ _ hi
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

structure DispatchSpecWalkC (p : ProgHOL 64) : Prop where
  run : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    s.code = originalRuntimeCode →
    (EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) →
    (evaluateHOLFiniteState s p).1 ≠ some .timeOut →
    ((evaluateHOLFiniteState s p).1 = none →
      (evaluateHOLFiniteState s p).2 = s) ∧
    ((evaluateHOLFiniteState s p).1 ≠ none →
      OpDispatchChainPost s (evaluateHOLFiniteState s p).1 (evaluateHOLFiniteState s p).2)

theorem DispatchSpecWalkC.skip : DispatchSpecWalkC .skip := by
  refine ⟨fun s _ _ _ => ?_⟩
  rw [evaluateHOLFiniteState_skip]
  exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

theorem DispatchSpecWalkC.raise (e : ExpHOL 64) :
    DispatchSpecWalkC (.raise (ofString "EvmErr") e) := by
  refine ⟨fun {F} s _ hRun _ => ⟨fun hn => (raise_ne_none s _ e hn).elim, fun _ => ?_⟩⟩
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · refine ⟨?_, fun _ => ?_⟩
      · rintro ⟨_, h⟩; cases h
      · have hInv' : EvmInv (emptyLocalsHOLFinite s) :=
          localsFree_evmInv s (emptyLocalsHOLFinite s).locals s.clock hRun.1
        have hWF' : HeadMemBridge.HeadMemChainWF (emptyLocalsHOLFinite s) :=
          HeadMemBridge.headMemChainWF_locals s (emptyLocalsHOLFinite s).locals s.clock hRun.2.1
        have hcongr := evm_congr (s := s) (t := emptyLocalsHOLFinite s) rfl rfl
        have hR : Wave8GuestInv.evmR (emptyLocalsHOLFinite s) ≤ Wave8GuestInv.evmR s :=
          le_of_eq hcongr.2.1
        exact ⟨⟨hInv', hWF'⟩, hcongr.2.2.1, hR⟩
    · exact opDispatchChainPost_error s s
  · exact opDispatchChainPost_error s s

theorem DispatchSpecWalkC.seqRaiseReturn (e1 e2 : ExpHOL 64) :
    DispatchSpecWalkC (.seq (.raise (ofString "EvmErr") e1) (.return e2)) := by
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
    have h1 := (DispatchSpecWalkC.raise e1).run s hcode hRun (by rw [hr]; exact hnt)
    rw [hr] at h1
    refine ⟨?_, fun _ => h1.2 (by simp)⟩
    intro h; cases h

private theorem return_const0_chainPost {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {v : ValueHOL 64}
    (hpost : OpDispatchChainPost (callEntryStateHOLFinite s callee) (some (.returned v)) cpost) :
    OpDispatchChainPost s
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
  have hInv_ret : EvmInv (emptyLocalsHOLFinite { cpost with locals := s.locals }) :=
    localsFree_evmInv cpost _ cpost.clock hInv_cp
  have hWF_ret : HeadMemBridge.HeadMemChainWF (emptyLocalsHOLFinite { cpost with locals := s.locals }) :=
    (HeadMemBridge.headMemChainWF_congr
      (s := cpost) (t := emptyLocalsHOLFinite { cpost with locals := s.locals }) rfl rfl).mpr hWF_cp
  refine ⟨fun _ => ⟨⟨hInv_ret, hWF_ret⟩, by rw [hcongr_ret.1, ← hcongr_ce.1]; exact hPot_cp⟩, ?_⟩
  rintro ⟨_, h⟩; cases h

private theorem call_exception_chainPost {F : Type} {s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {eid : MlS} {ev : ValueHOL 64}
    (hQ : OpDispatchChainPost (callEntryStateHOLFinite s callee) (some (.exception eid ev)) cpost) :
    OpDispatchChainPost s (some (.exception eid ev)) cpost.emptyLocalsHOLFinite := by
  by_cases heid : eid = ofString "EvmErr"
  · subst heid
    exact opDispatchChainPost_congr_lc (s := s) (s' := callEntryStateHOLFinite s callee)
      (post := cpost) (post' := cpost.emptyLocalsHOLFinite) rfl rfl rfl rfl rfl hQ
  · refine opDispatchChainPost_other (by intro _ h; cases h) ?_
    rintro ⟨_, h⟩
    injection h with h'; injection h' with h1 _; exact heid h1

private theorem evmChainRun_callEntry {F : Type} (s : PanSemStateFiniteExact 64 F)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (h : EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) :
    EvmInv (callEntryStateHOLFinite s callee) ∧
    HeadMemBridge.HeadMemChainWF (callEntryStateHOLFinite s callee) ∧
    ¬ EvmDone (callEntryStateHOLFinite s callee) := by
  have hrun := evmRun_callEntry s callee ⟨h.1, h.2.2⟩
  have hwf : HeadMemBridge.HeadMemChainWF (callEntryStateHOLFinite s callee) :=
    (HeadMemBridge.headMemChainWF_congr (s := s) (t := callEntryStateHOLFinite s callee) rfl rfl).mpr h.2.1
  exact ⟨hrun.1, hwf, hrun.2⟩

theorem DispatchSpecWalkC.callReturn {fname : MlS}
    (hf : OpHandlerChainSpec fname) (args : List (ExpHOL 64)) :
    DispatchSpecWalkC (.seq (.call (some (none, none)) fname args) (.return (.const 0))) := by
  refine ⟨fun {F} s hcode hRun hnt => ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩⟩
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite s
      (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | values
  · exact opDispatchChainPost_error s s
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchChainPost_error s s
    · simp only [hl] at hnt ⊢
      by_cases hz : s.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hce_code : (callEntryStateHOLFinite s callee).code = originalRuntimeCode := hcode
        have hce_run := evmChainRun_callEntry s callee hRun
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
        simp only [hrun] at hnt ⊢
        have hQ (hsafe : res ≠ some .timeOut) :
            OpDispatchChainPost (callEntryStateHOLFinite s callee) res cpost := by
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
        | none => exact opDispatchChainPost_error s cpost
        | some r0 =>
          cases r0 with
          | returned v =>
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
            · simp only [hsh, ↓reduceIte]
              exact return_const0_chainPost (hQ (by simp))
            · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchChainPost_error s cpost
          | timeOut => simp at hnt
          | exception eid ev => exact call_exception_chainPost (hQ (by simp))
          | «break» => exact opDispatchChainPost_error s cpost
          | «continue» => exact opDispatchChainPost_error s cpost
          | finalFfi f =>
            refine opDispatchChainPost_other (s := s) (t := cpost.emptyLocalsHOLFinite)
              (r := some (.finalFfi f)) (by intro _ h; cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchChainPost_error s cpost.emptyLocalsHOLFinite

theorem DispatchSpecWalkC.seq {p q : ProgHOL 64}
    (h1 : DispatchSpecWalkC p) (h2 : DispatchSpecWalkC q) :
    DispatchSpecWalkC (.seq p q) := by
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

theorem DispatchSpecWalkC.ite (c : ExpHOL 64) {p q : ProgHOL 64}
    (h1 : DispatchSpecWalkC p) (h2 : DispatchSpecWalkC q) :
    DispatchSpecWalkC (.ite c p q) := by
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
    refine ⟨?_, fun _ => opDispatchChainPost_error s s⟩
    intro h; cases h

private theorem callReturnC_one_word_bounded
    {fname paramName : MlS} {bound : Nat} {argExp : ExpHOL 64}
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    (hf : FunSpec
      (fun s => (EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) ∧
        ∃ w : BitVec 64, s.locals.lookup paramName = some (.val (.word w)) ∧ w.toNat ≤ bound)
      OpDispatchChainPost fname)
    (hlk_param : ∃ fbody, originalRuntimeCode.lookup fname = some ([(paramName, .one)], fbody, .one))
    (harg : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P s →
      ∃ w : BitVec 64,
        evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [argExp] =
          some [.val (.word w)] ∧
        w.toNat ≤ bound) :
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      s.code = originalRuntimeCode →
      (EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s) → P s →
      (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).1 ≠
        some .timeOut →
      OpDispatchChainPost s
        (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).1
        (evaluateHOLFiniteState s (.seq (.call (some (none, none)) fname [argExp]) (.return (.const 0)))).2 := by
  intro F s hcode hRun hPs hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  obtain ⟨fbody, hlk_exact⟩ := hlk_param
  obtain ⟨argw, harg_ev, harg_le⟩ := harg s hPs
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rw [harg_ev] at hnt ⊢; dsimp only at hnt ⊢
  rcases hl : lookupCodeHOLFinite s.code.lookup fname [.val (.word argw)] with _ | ⟨body', callee, ret'⟩
  · exact opDispatchChainPost_error s s
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
      have hce_pre : (EvmInv (callEntryStateHOLFinite s callee) ∧
          HeadMemBridge.HeadMemChainWF (callEntryStateHOLFinite s callee) ∧
          ¬ EvmDone (callEntryStateHOLFinite s callee)) ∧
          ∃ w : BitVec 64, (callEntryStateHOLFinite s callee).locals.lookup paramName =
            some (.val (.word w)) ∧ w.toNat ≤ bound :=
        ⟨evmChainRun_callEntry s callee hRun, argw, hcal_lk, harg_le⟩
      rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body' with ⟨res, cpost⟩
      simp only [hrun] at hnt ⊢
      have hQ (hsafe : res ≠ some .timeOut) :
          OpDispatchChainPost (callEntryStateHOLFinite s callee) res cpost := by
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
      | none => exact opDispatchChainPost_error s cpost
      | some r0 =>
        cases r0 with
        | returned v =>
          by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
          · simp only [hsh, ↓reduceIte]
            exact return_const0_chainPost (hQ (by simp))
          · simp only [hsh, Bool.false_eq_true, ↓reduceIte]
            exact opDispatchChainPost_error s cpost
        | timeOut => simp at hnt
        | exception eid ev => exact call_exception_chainPost (hQ (by simp))
        | «break» => exact opDispatchChainPost_error s cpost
        | «continue» => exact opDispatchChainPost_error s cpost
        | finalFfi f =>
          refine opDispatchChainPost_other (s := s) (t := cpost.emptyLocalsHOLFinite)
            (r := some (.finalFfi f)) (by intro _ h; cases h) ?_
          rintro ⟨_, h⟩; cases h
        | error => exact opDispatchChainPost_error s cpost.emptyLocalsHOLFinite

/-- Complete opcode handler bundle for `HeadMemBridge.OpDispatchSpecA` with range-bounded
`op_push` (`n ≤ 32`) and `op_log` (`ntopics ≤ 4`). -/
structure OpDispatchChainHandlersCutover : Prop where
  op_stop : OpHandlerChainSpec (ofString "op_stop")
  op_add : OpHandlerChainSpec (ofString "op_add")
  op_mul : OpHandlerChainSpec (ofString "op_mul")
  op_sub : OpHandlerChainSpec (ofString "op_sub")
  op_div : OpHandlerChainSpec (ofString "op_div")
  op_sdiv : OpHandlerChainSpec (ofString "op_sdiv")
  op_mod : OpHandlerChainSpec (ofString "op_mod")
  op_smod : OpHandlerChainSpec (ofString "op_smod")
  op_addmod : OpHandlerChainSpec (ofString "op_addmod")
  op_mulmod : OpHandlerChainSpec (ofString "op_mulmod")
  op_exp : OpHandlerChainSpec (ofString "op_exp")
  op_signextend : OpHandlerChainSpec (ofString "op_signextend")
  op_lt : OpHandlerChainSpec (ofString "op_lt")
  op_gt : OpHandlerChainSpec (ofString "op_gt")
  op_slt : OpHandlerChainSpec (ofString "op_slt")
  op_sgt : OpHandlerChainSpec (ofString "op_sgt")
  op_eq : OpHandlerChainSpec (ofString "op_eq")
  op_iszero : OpHandlerChainSpec (ofString "op_iszero")
  op_and : OpHandlerChainSpec (ofString "op_and")
  op_or : OpHandlerChainSpec (ofString "op_or")
  op_xor : OpHandlerChainSpec (ofString "op_xor")
  op_not : OpHandlerChainSpec (ofString "op_not")
  op_byte : OpHandlerChainSpec (ofString "op_byte")
  op_shl : OpHandlerChainSpec (ofString "op_shl")
  op_shr : OpHandlerChainSpec (ofString "op_shr")
  op_sar : OpHandlerChainSpec (ofString "op_sar")
  op_clz : OpHandlerChainSpec (ofString "op_clz")
  op_keccak : OpHandlerChainSpec (ofString "op_keccak")
  op_address : OpHandlerChainSpec (ofString "op_address")
  op_balance : OpHandlerChainSpec (ofString "op_balance")
  op_origin : OpHandlerChainSpec (ofString "op_origin")
  op_caller : OpHandlerChainSpec (ofString "op_caller")
  op_callvalue : OpHandlerChainSpec (ofString "op_callvalue")
  op_calldataload : OpHandlerChainSpec (ofString "op_calldataload")
  op_calldatasize : OpHandlerChainSpec (ofString "op_calldatasize")
  op_calldatacopy : OpHandlerChainSpec (ofString "op_calldatacopy")
  op_codesize : OpHandlerChainSpec (ofString "op_codesize")
  op_codecopy : OpHandlerChainSpec (ofString "op_codecopy")
  op_gasprice : OpHandlerChainSpec (ofString "op_gasprice")
  op_extcodesize : OpHandlerChainSpec (ofString "op_extcodesize")
  op_extcodecopy : OpHandlerChainSpec (ofString "op_extcodecopy")
  op_returndatasize : OpHandlerChainSpec (ofString "op_returndatasize")
  op_returndatacopy : OpHandlerChainSpec (ofString "op_returndatacopy")
  op_extcodehash : OpHandlerChainSpec (ofString "op_extcodehash")
  op_blockhash : OpHandlerChainSpec (ofString "op_blockhash")
  op_coinbase : OpHandlerChainSpec (ofString "op_coinbase")
  op_timestamp : OpHandlerChainSpec (ofString "op_timestamp")
  op_number : OpHandlerChainSpec (ofString "op_number")
  op_prevrandao : OpHandlerChainSpec (ofString "op_prevrandao")
  op_gaslimit : OpHandlerChainSpec (ofString "op_gaslimit")
  op_chainid : OpHandlerChainSpec (ofString "op_chainid")
  op_selfbalance : OpHandlerChainSpec (ofString "op_selfbalance")
  op_basefee : OpHandlerChainSpec (ofString "op_basefee")
  op_blobhash : OpHandlerChainSpec (ofString "op_blobhash")
  op_blobbasefee : OpHandlerChainSpec (ofString "op_blobbasefee")
  op_slotnum : OpHandlerChainSpec (ofString "op_slotnum")
  op_pop : OpHandlerChainSpec (ofString "op_pop")
  op_mload : OpHandlerChainSpec (ofString "op_mload")
  op_mstore : OpHandlerChainSpec (ofString "op_mstore")
  op_mstore8 : OpHandlerChainSpec (ofString "op_mstore8")
  op_sload : OpHandlerChainSpec (ofString "op_sload")
  op_sstore : OpHandlerChainSpec (ofString "op_sstore")
  op_jump : OpHandlerChainSpec (ofString "op_jump")
  op_jumpi : OpHandlerChainSpec (ofString "op_jumpi")
  op_pc : OpHandlerChainSpec (ofString "op_pc")
  op_msize : OpHandlerChainSpec (ofString "op_msize")
  op_gas : OpHandlerChainSpec (ofString "op_gas")
  op_jumpdest : OpHandlerChainSpec (ofString "op_jumpdest")
  op_tload : OpHandlerChainSpec (ofString "op_tload")
  op_tstore : OpHandlerChainSpec (ofString "op_tstore")
  op_mcopy : OpHandlerChainSpec (ofString "op_mcopy")
  op_push : OpPushBoundedChainSpec
  op_dup : OpHandlerChainSpec (ofString "op_dup")
  op_swap : OpHandlerChainSpec (ofString "op_swap")
  op_log : OpLogBoundedChainSpec
  op_dupn : OpHandlerChainSpec (ofString "op_dupn")
  op_swapn : OpHandlerChainSpec (ofString "op_swapn")
  op_exchange : OpHandlerChainSpec (ofString "op_exchange")
  op_create : OpHandlerChainSpec (ofString "op_create")
  op_call : OpHandlerChainSpec (ofString "op_call")
  op_callcode : OpHandlerChainSpec (ofString "op_callcode")
  op_return : OpHandlerChainSpec (ofString "op_return")
  op_delegatecall : OpHandlerChainSpec (ofString "op_delegatecall")
  op_create2 : OpHandlerChainSpec (ofString "op_create2")
  op_staticcall : OpHandlerChainSpec (ofString "op_staticcall")
  op_revert : OpHandlerChainSpec (ofString "op_revert")
  op_selfdestruct : OpHandlerChainSpec (ofString "op_selfdestruct")

private theorem push0_walkC (h_push : OpPushBoundedChainSpec) :
    DispatchSpecWalkC (.seq (.call (some (none, none)) (ofString "op_push") [.const 0#64]) (.return (.const 0))) := by
  refine ⟨fun {F} s hcode hRun hnt => ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩⟩
  exact callReturnC_one_word_bounded (P := fun _ => True) h_push ⟨_, lookup_op_push⟩
    (fun _ _ => ⟨0#64, rfl, by decide⟩) s hcode hRun trivial hnt

private theorem ite_push_sub95_walkC
    (h_op_push : OpPushBoundedChainSpec)
    {F : Type} (s : PanSemStateFiniteExact 64 F) {opw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hRun : EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
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
      OpDispatchChainPost s (evaluateHOLFiniteState s p_push).1 (evaluateHOLFiniteState s p_push).2) := by
  subst hp_eq
  rw [evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hlt : opw < 128#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hnt ⊢
    have hhi : opw.toNat < 128 := by simpa [BitVec.lt_def] using hlt
    refine ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩
    exact callReturnC_one_word_bounded
      (P := fun t => t.locals.lookup (ofString "op") = some (.val (.word opw)))
      h_op_push ⟨_, lookup_op_push⟩
      (fun t htop => ⟨opw - 95#64, evalList_sub_op_const t htop, push_arg_sub95_le_32 hlo hhi⟩)
      s hcode hRun hop hnt
  · simp only [hlt, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

private theorem ite_log_sub160_walkC
    (h_op_log : OpLogBoundedChainSpec)
    {F : Type} (s : PanSemStateFiniteExact 64 F) {opw : BitVec 64}
    (hcode : s.code = originalRuntimeCode)
    (hRun : EvmInv s ∧ HeadMemBridge.HeadMemChainWF s ∧ ¬ EvmDone s)
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
      OpDispatchChainPost s (evaluateHOLFiniteState s p_log).1 (evaluateHOLFiniteState s p_log).2) := by
  subst hp_eq
  rw [evaluateHOLFiniteState_ite, cmp_lower_op_eval s hop] at hnt ⊢
  dsimp only at hnt ⊢
  by_cases hlt : opw < 165#64
  · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
    simp only [hlt, ↓reduceIte, h10] at hnt ⊢
    have hhi : opw.toNat < 165 := by simpa [BitVec.lt_def] using hlt
    refine ⟨fun hn => (seq_return_ne_none s _ _ hn).elim, fun _ => ?_⟩
    exact callReturnC_one_word_bounded
      (P := fun t => t.locals.lookup (ofString "op") = some (.val (.word opw)))
      h_op_log ⟨_, lookup_op_log_cutover⟩
      (fun t htop => ⟨opw - 160#64, evalList_sub_op_const t htop, log_arg_sub160_le_4 hlo hhi⟩)
      s hcode hRun hop hnt
  · simp only [hlt, ↓reduceIte]
    rw [evaluateHOLFiniteState_skip]
    exact ⟨fun _ => rfl, fun h => (h rfl).elim⟩

private theorem walkC_group01 (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC dispatchGroup01 :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_stop _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_add _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_mul _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_sub _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_div _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_sdiv _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_mod _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_smod _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_addmod _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_mulmod _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_exp _) DispatchSpecWalkC.skip)
    (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_signextend _) DispatchSpecWalkC.skip)))))))))))

private theorem walkC_group02 (h : OpDispatchChainHandlersCutover)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkC tail) :
    DispatchSpecWalkC (dispatchGroup02 tail) :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_lt _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_gt _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_slt _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_sgt _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_eq _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_iszero _) DispatchSpecWalkC.skip)
    ht)))))

private theorem walkC_group03 (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC dispatchGroup03 :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_and _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_or _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_xor _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_not _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_byte _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_shl _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_shr _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_sar _) DispatchSpecWalkC.skip)
    (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_clz _) DispatchSpecWalkC.skip))))))))

private theorem walkC_group04 (h : OpDispatchChainHandlersCutover)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkC tail) :
    DispatchSpecWalkC (dispatchGroup04 tail) :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_keccak _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_address _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_balance _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_origin _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_caller _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_callvalue _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_calldataload _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_calldatasize _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_calldatacopy _) DispatchSpecWalkC.skip)
    ht))))))))

private theorem walkC_group05 (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC dispatchGroup05 :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_codesize _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_codecopy _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_gasprice _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_extcodesize _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_extcodecopy _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_returndatasize _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_returndatacopy _) DispatchSpecWalkC.skip)
    (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_extcodehash _) DispatchSpecWalkC.skip)))))))

private theorem walkC_group06 (h : OpDispatchChainHandlersCutover)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkC tail) :
    DispatchSpecWalkC (dispatchGroup06 tail) :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_blockhash _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_coinbase _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_timestamp _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_number _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_prevrandao _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_gaslimit _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_chainid _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_selfbalance _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_basefee _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_blobhash _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_blobbasefee _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_slotnum _) DispatchSpecWalkC.skip)
    ht)))))))))))

private theorem walkC_group07 (h : OpDispatchChainHandlersCutover)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkC tail) :
    DispatchSpecWalkC (dispatchGroup07 tail) :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_pop _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_mload _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_mstore _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_mstore8 _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_sload _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_sstore _) DispatchSpecWalkC.skip)
    ht)))))

private theorem walkC_group08 (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC dispatchGroup08 :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_jump _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_jumpi _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_pc _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_msize _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_gas _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_jumpdest _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_tload _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_tstore _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_mcopy _) DispatchSpecWalkC.skip)
    (DispatchSpecWalkC.ite _ (push0_walkC h.op_push) DispatchSpecWalkC.skip)))))))))

private theorem walkC_group11 (h : OpDispatchChainHandlersCutover)
    {tail : ProgHOL 64} (ht : DispatchSpecWalkC tail) :
    DispatchSpecWalkC (dispatchGroup11 tail) :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_create _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_call _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_callcode _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_return _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_delegatecall _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_create2 _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_staticcall _) DispatchSpecWalkC.skip)
    ht))))))

private theorem walkC_group12 (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC dispatchGroup12 :=
  DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_revert _) DispatchSpecWalkC.skip)
  (DispatchSpecWalkC.seq (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_selfdestruct _) DispatchSpecWalkC.skip)
    (DispatchSpecWalkC.seqRaiseReturn _ _))

private theorem walkC_group01_to_03 (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC (binaryAt [0] dispatchCode) :=
  DispatchSpecWalkC.ite _
    (DispatchSpecWalkC.seq
      (DispatchSpecWalkC.ite _ (walkC_group01 h) (walkC_group02 h (walkC_group03 h)))
      (DispatchSpecWalkC.raise _))
    DispatchSpecWalkC.skip

private theorem walkC_group04_to_08 (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC (binaryAt [1, 0] dispatchCode) :=
  DispatchSpecWalkC.ite _
    (DispatchSpecWalkC.seq
      (DispatchSpecWalkC.ite _
        (walkC_group04 h (walkC_group05 h))
        (walkC_group06 h (walkC_group07 h (walkC_group08 h))))
      (DispatchSpecWalkC.raise _))
    DispatchSpecWalkC.skip

private theorem walkC_dup_swap (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC (binaryAt [1, 1, 0, 0, 1] dispatchCode) :=
  DispatchSpecWalkC.seq
    (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_dup _) DispatchSpecWalkC.skip)
    (DispatchSpecWalkC.callReturn h.op_swap _)

private theorem walkC_after_log (h : OpDispatchChainHandlersCutover) :
    DispatchSpecWalkC (binaryAt [1, 1, 1, 1] dispatchCode) :=
  DispatchSpecWalkC.seq
    (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_dupn _) DispatchSpecWalkC.skip)
    (DispatchSpecWalkC.seq
      (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_swapn _) DispatchSpecWalkC.skip)
      (DispatchSpecWalkC.seq
        (DispatchSpecWalkC.ite _ (DispatchSpecWalkC.callReturn h.op_exchange _) DispatchSpecWalkC.skip)
        (walkC_group11 h (walkC_group12 h))))

/-- Chain-WF `op_dispatch` theorem: reduces `HeadMemBridge.OpDispatchSpecA` to
`OpDispatchChainHandlersCutover` (with bounded `op_push` `n ≤ 32` and bounded `op_log` `ntopics ≤ 4`). -/
theorem op_dispatch_chain_spec_cutover
    (h : OpDispatchChainHandlersCutover) :
    HeadMemBridge.OpDispatchSpecA := by
  have hlk_disp : originalRuntimeCode.lookup (ofString "op_dispatch") =
      some ([(ofString "op", .one)], dispatchCode, .one) := lookup_op_dispatch
  refine ⟨_, _, _, hlk_disp, ?_⟩
  intro F s hcode hRun hex hnt
  obtain ⟨opw, hop⟩ := op_dispatch_param_word hex
  change OpDispatchChainPost s (evaluateHOLFiniteState s dispatchCode).1 (evaluateHOLFiniteState s dispatchCode).2
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
    have hw0 := (walkC_group01_to_03 h).run s hcode hRun (by rw [hr0]; exact hnt)
    rw [hr0] at hw0
    exact hw0.2 (by simp)
  | none =>
    have hs1 : s = s1 := by
      have hw0 := (walkC_group01_to_03 h).run s hcode hRun (by rw [hr0]; simp)
      rw [hr0] at hw0; exact (hw0.1 rfl).symm
    subst hs1
    rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
    rcases hr1 : evaluateHOLFiniteState s p1 with ⟨r1, s2⟩
    simp only [hr1] at hnt ⊢
    cases r1 with
    | some _ =>
      have hw1 := (walkC_group04_to_08 h).run s hcode hRun (by rw [hr1]; exact hnt)
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
        have hgoal : OpDispatchChainPost s (evaluateHOLFiniteState s p2).1 (evaluateHOLFiniteState s p2).2 := by
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
              have hp := ite_push_sub95_walkC (p_push := p2_push)
                h.op_push s hcode hRun hop hge96 rfl
                (by rw [hpush]; exact hnt2)
              rw [hpush] at hp
              exact hp.2 (by simp)
            | none =>
              have hp := ite_push_sub95_walkC (p_push := p2_push)
                h.op_push s hcode hRun hop hge96 rfl
                (by rw [hpush]; simp)
              rw [hpush] at hp
              have hsp : s = sp := (hp.1 rfl).symm
              subst hsp
              dsimp only at hnt2 hr2 ⊢
              have hds := (walkC_dup_swap h).run s hcode hRun hnt2
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
          have hlogw := ite_log_sub160_walkC (p_log := p3) h.op_log s hcode hRun hop hge160 rfl
            (by rw [hr3]; exact hnt)
          rw [hr3] at hlogw
          exact hlogw.2 (by simp)
        | none =>
          have hlogw := ite_log_sub160_walkC (p_log := p3) h.op_log s hcode hRun hop hge160 rfl
            (by rw [hr3]; simp)
          rw [hr3] at hlogw
          have hs4 : s = s4 := (hlogw.1 rfl).symm
          subst hs4
          dsimp only at hnt ⊢
          rcases hr4 : evaluateHOLFiniteState s p4 with ⟨r4, s5⟩
          cases r4 with
          | none =>
            exact opDispatchChainPost_other (by intro _ hv; cases hv) (by rintro ⟨_, hv⟩; cases hv)
          | some _ =>
            have hw4 := (walkC_after_log h).run s hcode hRun hnt
            rw [hr4] at hw4
            exact hw4.2 (by simp)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
