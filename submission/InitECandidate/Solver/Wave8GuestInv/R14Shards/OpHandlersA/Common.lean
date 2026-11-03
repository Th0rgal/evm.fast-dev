import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.FrameBase

/-! # `EvmPreservingSpec`, `HandlerRun`, `charge_gas`, `pc_add`, and `stack_pop` -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. `EvmPreservingSpec` and `HandlerRun` combinators -/

def EvmPreservingSpec
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Qret : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      EvmInv s → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      let r := (evaluateHOLFiniteState s body).1
      let post := (evaluateHOLFiniteState s body).2
      (∀ v, r = some (.returned v) →
        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s ∧ Qret s v post) ∧
      (IsEvmErr r →
        EvmInv post ∧ evmChain post = evmChain s ∧ evmR post ≤ evmR s)

def HandlerRun {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (P : PanSemStateFiniteExact 64 F → Prop) (charged : Bool)
    (prog : ProgHOL 64) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 F),
    t.code = originalRuntimeCode →
    EvmInv t →
    (evmChain t).length = (evmChain s0).length →
    (if charged then evmR t < evmR s0 else evmR t ≤ evmR s0) →
    P t →
    (evaluateHOLFiniteState t prog).1 ≠ some .timeOut →
    OpDispatchPost s0 (evaluateHOLFiniteState t prog).1 (evaluateHOLFiniteState t prog).2

theorem opHandlerSpec_of_run (idx : Nat) (hidx : idx < Guest.Software.guestAst.length)
    (d : Decl (BitVec 64)) (hd : Guest.Software.guestAst[idx] = .function (extractFn d))
    (hrun : ∀ {F : Type} (s0 : PanSemStateFiniteExact 64 F), EvmRun s0 →
      HandlerRun s0 (fun _ => True) false
        (InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural (extractFn d).body)) :
    OpHandlerSpec (ofString (extractFn d).name) := by
  refine ⟨_, _, _, lookup_of_guestAst_getElem idx hidx (extractFn d) hd, ?_⟩
  intro F s0 hcode hRun _ hnt
  exact hrun s0 hRun s0 hcode hRun.1 rfl (le_refl _) trivial hnt

theorem HandlerRun.weaken {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} {prog : ProgHOL 64}
    (himp : ∀ t, EvmInv t → P t → Q t)
    (h : HandlerRun s0 Q charged prog) :
    HandlerRun s0 P charged prog :=
  fun t hc hInv hlen hR hP hnt => h t hc hInv hlen hR (himp t hInv hP) hnt

theorem HandlerRun.ret {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} (e : ExpHOL 64) :
    HandlerRun s0 P true (.return e) := by
  intro t _ hInv _ hR _ _
  simp only [↓reduceIte] at hR
  rw [evaluateHOLFiniteState_return]
  split
  · exact opDispatchPost_error s0 t
  · split
    · have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      refine ⟨fun _ => ⟨hInv', evmPot_lt_of_evmR_lt hInv' (by rw [hc.2.1]; exact hR)⟩, ?_⟩
      rintro ⟨_, h⟩; cases h
    · exact opDispatchPost_error s0 t

theorem HandlerRun.raise_evmErr {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} (e : ExpHOL 64) :
    HandlerRun s0 P charged (.raise (ofString "EvmErr") e) := by
  intro t _ hInv hlen hR _ _
  have hR_le : evmR t ≤ evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      refine ⟨?_, fun _ => ⟨hInv', by rw [hc.2.2.1]; exact hlen, by rw [hc.2.1]; exact hR_le⟩⟩
      rintro ⟨_, h⟩; cases h
    · exact opDispatchPost_error s0 t
  · exact opDispatchPost_error s0 t

theorem HandlerRun.raise_other {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} {eid : MlS}
    (hne : eid ≠ ofString "EvmErr") (e : ExpHOL 64) :
    HandlerRun s0 P charged (.raise eid e) := by
  intro t _ _ _ _ _ _
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · refine opDispatchPost_other (fun _ h => by cases h) ?_
      rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact hne h1
    · exact opDispatchPost_error s0 t
  · exact opDispatchPost_error s0 t

theorem HandlerRun.dec {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hinit : ∀ t v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) init = some v →
      EvmInv t → P t → Q (setVarHOLFinite nm v t))
    (hbody : HandlerRun s0 Q charged body) :
    HandlerRun s0 P charged (.dec nm sh init body) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_dec_total] at hnt ⊢
  dsimp only at hnt ⊢
  revert hnt
  split
  · intro _; exact opDispatchPost_error s0 t
  · rename_i v hv
    split
    · intro hnt
      let t1 := setVarHOLFinite nm v t
      have hInv1 : EvmInv t1 := localsFree_evmInv t t1.locals t.clock hInv
      have hc1 := evm_congr (s := t) (t := t1) rfl rfl
      have hR1 : if charged then evmR t1 < evmR s0 else evmR t1 ≤ evmR s0 := by
        rw [hc1.2.1]; exact hR
      have hb := hbody t1 hc hInv1 (hc1.2.2.1.trans hlen) hR1 (hinit t v hv hInv hP) hnt
      exact opDispatchPost_congr_lc rfl rfl rfl hb
    · intro _; exact opDispatchPost_error s0 t

theorem HandlerRun.dec_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {nm : MlS} {sh : ShapeHOL} {init : ExpHOL 64} {body : ProgHOL 64}
    (hbody : HandlerRun s0 (fun _ => True) charged body) :
    HandlerRun s0 (fun _ => True) charged (.dec nm sh init body) :=
  HandlerRun.dec (fun _ _ _ _ _ => trivial) hbody

theorem HandlerRun.seq_assign_local {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {exp : ExpHOL 64} {cont : ProgHOL 64}
    (hasgn : ∀ t v,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) exp = some v →
      EvmInv t → P t → Q (setKvarHOLFinite .local nm v t))
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged (.seq (.assign .local nm exp) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt ⊢
  revert hnt
  split
  · intro _; exact opDispatchPost_error s0 t
  · rename_i v hv
    split
    · dsimp only; intro hnt
      let t1 := setKvarHOLFinite .local nm v t
      have hInv1 : EvmInv t1 := localsFree_evmInv t t1.locals t.clock hInv
      have hc1 := evm_congr (s := t) (t := t1) rfl rfl
      have hR1 : if charged then evmR t1 < evmR s0 else evmR t1 ≤ evmR s0 := by
        rw [hc1.2.1]; exact hR
      exact hcont t1 hc hInv1 (hc1.2.2.1.trans hlen) hR1 (hasgn t v hv hInv hP) hnt
    · intro _; exact opDispatchPost_error s0 t

theorem HandlerRun.ite {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {yes no : ProgHOL 64}
    (hyes : HandlerRun s0 (fun t => P t ∧
      ∃ w : BitVec 64, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word w)) ∧ w ≠ 0) charged yes)
    (hno : HandlerRun s0 (fun t => P t ∧
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0))) charged no) :
    HandlerRun s0 P charged (.ite cond yes no) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]
      intro hnt; exact hno t hc hInv hlen hR ⟨hP, hw⟩ hnt
    · simp only [hw0, ↓reduceIte]
      intro hnt; exact hyes t hc hInv hlen hR ⟨hP, w, hw, hw0⟩ hnt
  · intro _; exact opDispatchPost_error s0 t

theorem HandlerRun.seq_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool} {cont : ProgHOL 64}
    (hcont : HandlerRun s0 P charged cont) :
    HandlerRun s0 P charged (.seq .skip cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hnt ⊢
  exact hcont t hc hInv hlen hR hP hnt

theorem HandlerRun.seq_ite_raise_skip {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {cond : ExpHOL 64} {errExp : ExpHOL 64} {cont : ProgHOL 64}
    (hfalse : ∀ t,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0)) →
      EvmInv t → P t → Q t)
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged (.seq (.ite cond (.raise (ofString "EvmErr") errExp) .skip) cont) := by
  intro t hc hInv hlen hR hP hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hw
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      intro hnt; exact hcont t hc hInv hlen hR (hfalse t hw hInv hP) hnt
    · simp only [hw0, ↓reduceIte]
      rcases hraise : evaluateHOLFiniteState t (.raise (ofString "EvmErr") errExp) with ⟨rr, sr⟩
      cases rr with
      | none => exact absurd hraise (fun h => raise_ne_none t _ errExp (by rw [h]))
      | some r0 =>
        dsimp only; intro hnt
        have hr := (HandlerRun.raise_evmErr (P := P) (charged := charged) errExp) t hc hInv hlen hR hP
          (by rw [hraise]; exact hnt)
        rw [hraise] at hr; exact hr
  · intro _; exact opDispatchPost_error s0 t

private theorem rbound_step {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem rbound_to_le {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

theorem HandlerRun.decCall {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged (.decCall nm sh fname args cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
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
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hInv hP hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rbound_step (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              have hb := hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
              exact opDispatchPost_congr_lc rfl rfl rfl hb
            · exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rbound_to_le hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRun.decCall_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {nm : MlS} {sh : ShapeHOL} {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec (fun _ => True) Qc fname)
    (hcont : HandlerRun s0 (fun _ => True) charged cont) :
    HandlerRun s0 (fun _ => True) charged (.decCall nm sh fname args cont) :=
  HandlerRun.decCall hf (fun _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hcont

theorem HandlerRun.seq_call {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec Pc Qc fname)
    (hentry : ∀ t values body' callee ret',
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ t values body callee retShape v cpost,
      EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      EvmInv cpost → evmChain cpost = evmChain (callEntryStateHOLFinite t callee) →
      Qc (callEntryStateHOLFinite t callee) v cpost →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
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
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hInv hP hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hQ (hsafe : res ≠ some .timeOut) :
            (∀ v, res = some (.returned v) →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee) ∧
              Qc (callEntryStateHOLFinite t callee) v cpost) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ evmChain cpost = evmChain (callEntryStateHOLFinite t callee) ∧
              evmR cpost ≤ evmR (callEntryStateHOLFinite t callee)) := by
          have hs := hspec (callEntryStateHOLFinite t callee) hc hInv_ce hPc ⟨values, hl_orig⟩
            (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact hs
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rbound_step (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              exact hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · have := rbound_to_le hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRun.seq_call_simple {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {Qc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hf : EvmPreservingSpec (fun _ => True) Qc fname)
    (hcont : HandlerRun s0 (fun _ => True) charged cont) :
    HandlerRun s0 (fun _ => True) charged (.seq (.call (some (none, none)) fname args) cont) :=
  HandlerRun.seq_call hf (fun _ _ _ _ _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) hcont

/-! ## 2. Exact `charge_gas` strict `evmR` decrease rule -/

theorem one_word_arg_lookup {fname param : MlS} {body : ProgHOL 64}
    {v0 : ValueHOL 64} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hlook : originalRuntimeCode.lookup fname = some ([(param, .one)], body, .one))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname [v0] = some (body', callee, ret')) :
    body' = body ∧ ret' = .one ∧ ∃ w : BitVec 64, v0 = .val (.word w) ∧ callee.lookup param = some (.val (.word w)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname [v0] body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
  split at hx
  · rename_i hcond
    have heq := Option.some.inj hx
    rcases Prod.mk.inj heq with ⟨rfl, hrest⟩
    rcases Prod.mk.inj hrest with ⟨hloc, rfl⟩
    have hsh : shapeEqHOL .one (shapeOfHOLExact v0) = true := by simpa [List.map] using hcond
    rcases v0 with ⟨⟨w⟩⟩ | _ | _
    · refine ⟨rfl, rfl, w, rfl, ?_⟩
      have hfn := congrFun hloc.symm param
      simpa [FUPDATE_LIST, FUPDATE] using hfn
    · simp [shapeOfHOLExact, shapeEqHOL] at hsh
    · simp [shapeOfHOLExact, shapeEqHOL] at hsh
  · cases hx

private theorem store_some_eq_error {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · rcases dv with ⟨⟨addr⟩⟩ | _ | _
    · rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
      · intro h; injection h with h1; injection h1 with h2; exact h2.symm
      · dsimp only
        split
        · intro h; injection h with h1; cases h1
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    · intro h; injection h with h1; injection h1 with h2; exact h2.symm

theorem charge_gas_body_exact {F : Type} (s : PanSemStateFiniteExact 64 F)
    (hInv : EvmInv s) {amtw : BitVec 64}
    (hamt : s.locals.lookup (ofString "amount") = some (.val (.word amtw))) :
    let out := evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_charge_gas)
    (∀ v, out.1 = some (.returned v) →
      EvmInv out.2 ∧ out.2.globals = s.globals ∧ evmChain out.2 = evmChain s ∧
      evmR out.2 + amtw.toNat = evmR s) ∧
    (IsEvmErr out.1 →
      EvmInv out.2 ∧ out.2.globals = s.globals ∧ evmChain out.2 = evmChain s ∧
      evmR out.2 = evmR s) := by
  dsimp only
  have hch_cons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
  obtain ⟨chTail, hch_eq⟩ := hch_cons
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_self
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    have hin := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  have hev64 : evw + BitVec.ofNat 64 64 = BitVec.ofNat 64 (globN s "ev" + 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hev184 : evw + BitVec.ofNat 64 184 = BitVec.ofNat 64 (globN s "ev" + 184) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat]
  have hno_ret_err {r0 : Option (PanSemResultExact 64)} {P1 P2 : Prop}
      (h1 : ∀ v, r0 ≠ some (.returned v)) (h2 : ¬ IsEvmErr r0) :
      (∀ v, r0 = some (.returned v) → P1) ∧ (IsEvmErr r0 → P2) :=
    ⟨fun v hv => (h1 v hv).elim, fun he => (h2 he).elim⟩
  have herr_triv {P1 P2 : Prop} :
      (∀ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v) → P1) ∧
      (IsEvmErr (some PanSemResultExact.error) → P2) :=
    hno_ret_err (fun _ h => by cases h) (by rintro ⟨_, h⟩; cases h)
  have hbody : sourceFnBody Guest.Software.guestFn_charge_gas =
      .dec (ofString "gl") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 64]))
        (.seq
          (.ite (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount")))
            (.raise (ofString "EvmErr") (.const 4))
            .skip)
          (.seq
            (.store (.op .add [.var .global (ofString "ev"), .const 64])
              (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 184])
                (.op .add
                  [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                   .var .local (ofString "amount")]))
              (.return (.const 0))))) := rfl
  rw [hbody, evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · exact herr_triv
  · rename_i glv hgl
    have hgl_w : ∃ glw : BitVec 64, glv = .val (.word glw) ∧ glw.toNat = memW s (globN s "ev" + 64) := by
      simp [evalHOLExact, evalListHOLExact, hevw, valueIsWord, valueWord, wordOpHOL, wordOp, memLoadHOLExact] at hgl
      rcases hm : s.memory (evw + 64#64) with ⟨glw⟩
      rw [hm] at hgl
      exact ⟨glw, hgl.2.symm, by unfold memW; rw [← hev64, hm]⟩
    obtain ⟨glw, rfl, hglw_eq⟩ := hgl_w
    have hsh_gl : shapeEqHOL .one (shapeOfHOLExact (.val (.word glw) : ValueHOL 64)) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos hsh_gl]; dsimp only
    set s1 := setVarHOLFinite (ofString "gl") (.val (.word glw)) s with hs1
    have hs1_gl : s1.locals.lookup (ofString "gl") = some (.val (.word glw)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hs1_amt : s1.locals.lookup (ofString "amount") = some (.val (.word amtw)) := by
      simp [hs1, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hamt,
        show ofString "gl" ≠ ofString "amount" by decide]
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
    have hcmp : @evalHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a))
        (.cmp .lower (.var .local (ofString "gl")) (.var .local (ofString "amount"))) =
        some (.val (.word (if glw < amtw then 1 else 0))) := by
      simp [evalHOLExact, hs1_gl, hs1_amt, Compiler.Encoders.Asm.wordCmpHOL]
    rw [hcmp]; dsimp only
    by_cases hlt : glw < amtw
    · have h10 : ¬ ((1 : BitVec 64) = 0) := by decide
      simp only [hlt, ↓reduceIte, h10]
      rw [evaluateHOLFiniteState_raise]; dsimp only [evalHOLExact]
      cases hs1_esh : s1.eshapes.lookup (ofString "EvmErr") with
      | none =>
        dsimp only
        exact herr_triv
      | some sh =>
        dsimp only
        by_cases hcond : shapeOfHOLExact (.val (.word (4 : BitVec 64))) = sh ∧
            sizeOfShapeWithContextHOL s1.structs (shapeOfHOLExact (.val (.word (4 : BitVec 64)))) ≤ 32
        · rw [if_pos hcond]; dsimp only
          let post := { (emptyLocalsHOLFinite s1) with
            locals := (emptyLocalsHOLFinite s1).locals.resVarEq (ofString "gl", s.locals.lookup (ofString "gl")) }
          have hInv_p : EvmInv post := localsFree_evmInv s post.locals s.clock hInv
          have hc_p := evm_congr (s := s) (t := post) rfl rfl
          constructor
          · intro _ h; cases h
          · intro _
            exact ⟨hInv_p, rfl, evmChain_congr rfl rfl, hc_p.2.1⟩
        · rw [if_neg hcond]; dsimp only
          exact herr_triv
    · have hamt_le : amtw.toNat ≤ glw.toNat := by rw [BitVec.lt_def] at hlt; omega
      simp only [hlt, ↓reduceIte, evaluateHOLFiniteState_skip]
      rw [evaluateHOLFiniteState_seq_line780]
      rcases hst1 : evaluateHOLFiniteState s1
          (.store (.op .add [.var .global (ofString "ev"), .const 64])
            (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
      cases r1 with
      | some res1 =>
        have herr1 := store_some_eq_error hst1; subst herr1
        dsimp only
        exact herr_triv
      | none =>
        dsimp only
        obtain ⟨w1, hw1_ev, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
          (gname := "ev") (gbase := globN s "ev") (off := 64) hevw hevw_nat (by omega)
          (fun v hv => by
            simp [evalHOLExact, evalListHOLExact, hs1_gl, hs1_amt, valueIsWord, valueWord, wordOpHOL, wordOp] at hv
            exact ⟨_, hv.symm⟩) hst1
        have hw1_val : w1 = glw - amtw := by
          simp [evalHOLExact, evalListHOLExact, hs1_gl, hs1_amt, valueIsWord, valueWord, wordOpHOL, wordOp] at hw1_ev
          exact hw1_ev.symm
        subst hw1_val
        rw [evaluateHOLFiniteState_seq_line780]
        rcases hst2 : evaluateHOLFiniteState s2
            (.store (.op .add [.var .global (ofString "ev"), .const 184])
              (.op .add
                [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                 .var .local (ofString "amount")])) with ⟨r2, s3⟩
        cases r2 with
        | some res2 =>
          have herr2 := store_some_eq_error hst2; subst herr2
          dsimp only
          exact herr_triv
        | none =>
          dsimp only
          obtain ⟨w2, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
            (gname := "ev") (gbase := globN s "ev") (off := 184)
            (by rw [hs2_eq]; exact hevw) hevw_nat (by omega)
            (fun v hv => by
              simp only [evalHOLExact, wordOpHOL] at hv; revert hv
              rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
              · simp
              · dsimp only; split
                · simp only [Option.map]
                  rcases wordOp .add (vs.map valueWord) with _ | w
                  · simp
                  · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                · simp) hst2
          rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact]
          have hsz0 : sizeOfShapeWithContextHOL s3.structs
              (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0]; dsimp only
          let post := { (emptyLocalsHOLFinite s3) with
            locals := (emptyLocalsHOLFinite s3).locals.resVarEq (ofString "gl", s.locals.lookup (ofString "gl")) }
          have hGp : GuestInv post := guestInv_congr (s := s)
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            (by simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite])
            hInv.1.1
          have hglob_p : post.globals = s.globals := by
            simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite]
          have hbe_p : post.be = s.be := by
            simp [post, emptyLocalsHOLFinite, hs3_eq, hs2_eq, hs1, setVarHOLFinite]
          have hmem_ne : ∀ a : Nat, a < 2 ^ 64 → a ≠ globN s "ev" + 64 → a ≠ globN s "ev" + 184 →
              memW post a = memW s a := by
            intro a ha hne64 hne184
            change memW s3 a = memW s a
            rw [hs3_eq, memW_updW_ne s2 _ a w2 (by omega) ha hne184,
                hs2_eq, memW_updW_ne s1 _ a (glw - amtw) (by omega) ha hne64]
            rfl
          have hm64 : memW post (globN s "ev" + 64) = memW s (globN s "ev" + 64) - amtw.toNat := by
            change memW s3 (globN s "ev" + 64) = _
            rw [hs3_eq, memW_updW_ne s2 _ _ w2 (by omega) (by omega) (by omega),
                hs2_eq, memW_updW_same s1 _ (glw - amtw),
                BitVec.toNat_sub_of_le (BitVec.le_def.2 hamt_le), hglw_eq]
          have hm192 : memW post (globN s "ev" + 192) = memW s (globN s "ev" + 192) :=
            hmem_ne _ (by omega) (by omega) (by omega)
          have hmem_out : ∀ x : BitVec 64,
              (∀ addr ∈ headAllowedOffsets (globN s "ev") (globN s "cur_cont"), x ≠ BitVec.ofNat 64 addr) →
              post.memory x = s.memory x := by
            intro x hx
            change s3.memory x = s.memory x
            rw [hs3_eq, hs2_eq]
            have hn184 : x ≠ BitVec.ofNat 64 (globN s "ev" + 184) := hx _ (by simp [headAllowedOffsets])
            have hn64 : x ≠ BitVec.ofNat 64 (globN s "ev" + 64) := hx _ (by simp [headAllowedOffsets])
            simp [updW, hn184, hn64, hs1, setVarHOLFinite]
          obtain ⟨hInv_p, hch_p, _⟩ := evmInv_of_head_status_gas_update hInv hGp hglob_p hbe_p hmem_out
            (by rw [hm64, hm192]; omega)
          have hR_sum : evmR post + amtw.toNat = evmR s := by
            have htail_eq : (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)) =
                (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)) := by
              apply List.map_congr_left; intro ec htail
              have hec : ec ∈ evmChain s := by rw [hch_eq]; exact List.mem_cons_of_mem _ htail
              have hb_ec := (frameWF_bounds hInv.1.2 (hInv.2.choose_spec.2.2.2.2.1 ec hec)).1
              have hFO_pw := hInv.2.choose_spec.2.2.2.2.2.2.2.1
              rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw
              have hd := hFO_pw.2.2 (globN s "ev", 280) (by simp [frameObjects]) (ec.1, 280)
                (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, htail, rfl⟩, by simp [frameObjects]⟩)
              have hne_ec : ∀ off1 off2, off1 + 8 ≤ 280 → off2 + 8 ≤ 280 →
                  ec.1 + off1 ≠ globN s "ev" + off2 := by
                intro off1 off2 _ _ heq
                rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
              rw [hmem_ne (ec.1 + 64) (by omega) (hne_ec 64 64 (by omega) (by omega)) (hne_ec 64 184 (by omega) (by omega)),
                  hmem_ne (ec.1 + 192) (by omega) (hne_ec 192 64 (by omega) (by omega)) (hne_ec 192 184 (by omega) (by omega))]
            have hsum_eq : ((chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum) =
                ((chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum) :=
              congrArg List.sum htail_eq
            have hpost_R : evmR post = (memW post (globN s "ev" + 64) + memW post (globN s "ev" + 192)) +
                (chTail.map fun ec => memW post (ec.1 + 64) + memW post (ec.1 + 192)).sum := by
              unfold evmR; rw [hch_p, hch_eq, List.map_cons, List.sum_cons]
            have hs_R : evmR s = (memW s (globN s "ev" + 64) + memW s (globN s "ev" + 192)) +
                (chTail.map fun ec => memW s (ec.1 + 64) + memW s (ec.1 + 192)).sum := by
              unfold evmR; rw [hch_eq, List.map_cons, List.sum_cons]
            rw [hpost_R, hs_R, hm64, hm192, hsum_eq]
            have : amtw.toNat ≤ memW s (globN s "ev" + 64) := by rw [← hglw_eq]; exact hamt_le
            omega
          exact ⟨fun _ _ => ⟨hInv_p, hglob_p, hch_p, hR_sum⟩, by rintro ⟨_, h⟩; cases h⟩

theorem HandlerRun.seq_charge_gas {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost,
      EvmInv t → P t → EvmInv cpost → cpost.globals = t.globals →
      evmChain cpost = evmChain t →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRun s0 Q true cont) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hInv hlen hR hP hnt
  have hR_le : evmR t ≤ evmR s0 := rbound_to_le hR
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact opDispatchPost_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp = some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hInv hP
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exact (callEntryStateHOLFinite t callee) hInv_ce hamt_cal
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
            (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta hcg ⊢
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : evmR resumed < evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              exact hcont resumed (hmeta.trans hc) hInv_res hlen_res (by simp [hR_lt])
                (hstep t cpost hInv hP hInv_cp hglob_cp (hch_cp.trans (evmChain_congr rfl rfl)))
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1, hR_cp, hc_ce.2.1]; exact hR_le
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRun.seq_charge_gas_const {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {charged : Bool} {k : BitVec 64} (hk : 0 < k.toNat) {cont : ProgHOL 64}
    (hcont : HandlerRun s0 (fun _ => True) true cont) :
    HandlerRun s0 (fun _ => True) charged (.seq (.call (some (none, none)) (ofString "charge_gas") [.const k]) cont) :=
  HandlerRun.seq_charge_gas
    (fun _ w hw _ _ => by simp only [evalHOLExact] at hw; injection hw with h1; injection h1 with h2; injection h2 with h3; subst h3; exact hk)
    (fun _ _ _ _ _ _ _ => trivial)
    hcont

/-! ## 3. Core `EvmPreservingSpec` instances: `pc_add` and `stack_pop` -/

theorem lookup_pc_add :
    originalRuntimeCode.lookup (ofString "pc_add") =
      some ([(ofString "n", .one)], sourceFnBody Guest.Software.guestFn_pc_add, .one) :=
  lookup_of_guestAst_getElem 468 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_pc_add) rfl

theorem eps_pc_add :
    EvmPreservingSpec (fun _ => True) (fun s _ post => post.globals = s.globals) (ofString "pc_add") := by
  refine ⟨_, _, _, lookup_pc_add, ?_⟩
  intro F s _ hInv _ _ _
  have hbody : sourceFnBody Guest.Software.guestFn_pc_add =
      .seq
        (.store (.op .add [.var .global (ofString "ev"), .const 0])
          (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")]))
        (.return (.const 0)) := rfl
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    have hin := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
  dsimp only; rw [hbody, evaluateHOLFiniteState_seq_line780]
  rcases hst : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 0])
        (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")])) with ⟨r1, s1⟩
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_error hst; subst herr
    dsimp only
    constructor
    · intro _ h; cases h
    · rintro ⟨_, h⟩; cases h
  | none =>
    dsimp only
    obtain ⟨w1, _, hs1_eq⟩ := store_global_off_word (t := s) (post := s1)
      (gname := "ev") (gbase := globN s "ev") (off := 0) hevw hevw_nat (by omega)
      (fun v hv => by
        simp only [evalHOLExact, wordOpHOL] at hv; revert hv
        rcases @evalListHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) _ with _ | vs
        · simp
        · dsimp only; split
          · simp only [Option.map]
            rcases wordOp .add (vs.map valueWord) with _ | w
            · simp
            · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
          · simp) hst
    rw [evaluateHOLFiniteState_return]; dsimp only [evalHOLExact]
    have hsz0 : sizeOfShapeWithContextHOL s1.structs
        (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
      simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    rw [if_pos hsz0]; dsimp only
    let post := emptyLocalsHOLFinite s1
    have hGp : GuestInv post := guestInv_congr (s := s)
      (by simp [post, emptyLocalsHOLFinite, hs1_eq])
      (by simp [post, emptyLocalsHOLFinite, hs1_eq])
      (by simp [post, emptyLocalsHOLFinite, hs1_eq])
      (by simp [post, emptyLocalsHOLFinite, hs1_eq])
      hInv.1.1
    have hglob_p : post.globals = s.globals := by simp [post, emptyLocalsHOLFinite, hs1_eq]
    have hbe_p : post.be = s.be := by simp [post, emptyLocalsHOLFinite, hs1_eq]
    have hmem_out : ∀ x : BitVec 64,
        (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN s "ev" + off)) →
        post.memory x = s.memory x := by
      intro x hx
      change s1.memory x = s.memory x
      rw [hs1_eq]; dsimp only [updW]
      have hn0 : x ≠ BitVec.ofNat 64 (globN s "ev" + 0) := hx 0 (by simp [nonStructFrameOffs])
      rw [if_neg hn0]
    obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_nonstruct hInv hGp hglob_p hbe_p hmem_out
    exact ⟨fun _ _ => ⟨hInv_p, hch_p, le_of_eq hR_p, hglob_p⟩, by rintro ⟨_, h⟩; cases h⟩

theorem lookup_stack_pop_pub :
    originalRuntimeCode.lookup (ofString "stack_pop") =
      some ([], sourceFnBody Guest.Software.guestFn_stack_pop, .comb [.one, .one, .one, .one]) :=
  lookup_of_guestAst_getElem 453 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_stack_pop) rfl

theorem eps_stack_pop :
    EvmPreservingSpec (fun _ => True) (fun s _ post => post.globals = s.globals) (ofString "stack_pop") := by
  refine ⟨_, _, _, lookup_stack_pop_pub, ?_⟩
  intro F s hcode hInv _ hlookup hnt
  let retExp : ExpHOL 64 :=
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural
      (Exp.load (Shape.comb [Shape.one, Shape.one, Shape.one, Shape.one])
        (Exp.op BinOp.add [(Exp.load Shape.one (Exp.op BinOp.add [(Exp.var VarKind.global "ev"), (Exp.const (BitVec.ofNat 64 8))])),
          (Exp.panOp PanOp.mul [(Exp.var VarKind.local "sp"), (Exp.const (BitVec.ofNat 64 32))])]))
  have hb : sourceFnBody Guest.Software.guestFn_stack_pop =
      .dec (ofString "sp") .one (.load .one (.op .add [.var .global (ofString "ev"), .const 16]))
        (.seq
          (.ite (.cmp .equal (.var .local (ofString "sp")) (.const 0))
            (.raise (ofString "EvmErr") (.const 2))
            .skip)
          (.seq
            (.assign .local (ofString "sp") (.op .sub [.var .local (ofString "sp"), .const 1]))
            (.seq
              (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp")))
              (.return retExp)))) := rfl
  obtain ⟨params_sp, body_sp, ret_sp, hlk_sp, hspec_sp⟩ := ek_stack_pop
  have hlk_eq : some ([], sourceFnBody Guest.Software.guestFn_stack_pop, ShapeHOL.comb [.one, .one, .one, .one]) =
      some (params_sp, body_sp, ret_sp) := lookup_stack_pop_pub.symm.trans hlk_sp
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_sp, rfl⟩
  subst hbody_sp
  have hstep_res (hres : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).1) :
      EvmInv (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2 ∧
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2.globals = s.globals ∧
      evmChain (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2 = evmChain s ∧
      evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2 = evmR s := by
    have hek := hspec_sp s hcode hInv hlookup hnt hres
    have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
    have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
    have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
    dsimp only at hb_ev
    have hev_pos : 0 < globN s "ev" := by
      have hin := (hFW0.1 (globN s "ev", 280) (by simp)).1.1
      have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
      rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
    obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
    have hmem_glob :
        let post := (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2
        post.globals = s.globals ∧ ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 16) → post.memory x = s.memory x := by
      dsimp only
      have hnot_err : ¬ Resumes (some (.error : PanSemResultExact 64)) := by
        rintro (⟨_, h⟩ | ⟨_, _, h, _⟩) <;> cases h
      revert hres
      rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
      split
      · intro hres; exact absurd hres hnot_err
      · rename_i vsp _
        split
        · dsimp only
          set s1 := setVarHOLFinite (ofString "sp") vsp s
          rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite]
          split
          · split
            · simp only [evaluateHOLFiniteState_skip]
              rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign]
              split
              · intro hres; exact absurd hres hnot_err
              · rename_i sp1 hsp1
                have hsp1_w : ∃ w : BitVec 64, sp1 = .val (.word w) := by
                  simp only [evalHOLExact, wordOpHOL] at hsp1; revert hsp1
                  rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                  · simp
                  · dsimp only; split
                    · simp only [Option.map]
                      rcases wordOp .sub (vs.map valueWord) with _ | w
                      · simp
                      · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                    · simp
                obtain ⟨spw, rfl⟩ := hsp1_w
                split
                · dsimp only
                  set s2 := setKvarHOLFinite .local (ofString "sp") (.val (.word spw)) s1
                  rw [evaluateHOLFiniteState_seq_line780]
                  rcases hst : evaluateHOLFiniteState s2
                      (.store (.op .add [.var .global (ofString "ev"), .const 16]) (.var .local (ofString "sp"))) with ⟨r2, s3⟩
                  cases r2 with
                  | some res2 =>
                    have herr := store_some_eq_error hst; subst herr
                    dsimp only
                    intro hres; exact absurd hres hnot_err
                  | none =>
                    dsimp only
                    obtain ⟨w2, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                      (gname := "ev") (gbase := globN s "ev") (off := 16) hevw hevw_nat (by omega)
                      (fun v hv => by
                        have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                          simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                        change s2.locals.lookup (ofString "sp") = some v at hv
                        rw [hsp2] at hv; injection hv with hv'; exact ⟨spw, hv'.symm⟩) hst
                    intro _
                    rw [evaluateHOLFiniteState_return]
                    split
                    · refine ⟨by simp [hs3_eq, s2, s1, setKvarHOLFinite, setVarHOLFinite], fun x hx => ?_⟩
                      dsimp only; rw [hs3_eq]; dsimp only [updW]; rw [if_neg hx]; rfl
                    · split
                      · refine ⟨by simp [emptyLocalsHOLFinite, hs3_eq, s2, s1, setKvarHOLFinite, setVarHOLFinite], fun x hx => ?_⟩
                        dsimp only [emptyLocalsHOLFinite]; rw [hs3_eq]; dsimp only [updW]; rw [if_neg hx]; rfl
                      · refine ⟨by simp [hs3_eq, s2, s1, setKvarHOLFinite, setVarHOLFinite], fun x hx => ?_⟩
                        dsimp only; rw [hs3_eq]; dsimp only [updW]; rw [if_neg hx]; rfl
                · intro hres; exact absurd hres hnot_err
            · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
              have hr_nn : rr ≠ none ∧ sr.globals = s.globals ∧ sr.memory = s.memory := by
                rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                split at hraise
                · split at hraise <;> (injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩)
                · injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩
              cases rr with
              | none => exact absurd rfl hr_nn.1
              | some _ =>
                dsimp only; intro _
                exact ⟨hr_nn.2.1, fun x _ => by change sr.memory x = s.memory x; rw [hr_nn.2.2]⟩
          · intro hres; exact absurd hres hnot_err
        · intro hres; exact absurd hres hnot_err
    obtain ⟨hglob_p, hmem_p⟩ := hmem_glob
    have hch_cons : ∃ tl, evmChain s = (globN s "ev", globN s "cur_cont") :: tl := ⟨_, rfl⟩
    obtain ⟨chTail, hch_eq⟩ := hch_cons
    have hR_eq : evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2 = evmR s := by
      refine evmR_eq_of_chain_and_words hek.2.2.2 (fun ec hec => ?_)
      have hb_ec := (frameWF_bounds hInv.1.2 (hInv.2.choose_spec.2.2.2.2.1 ec hec)).1
      have hne_ec : ∀ off, off + 8 ≤ 280 → off ≠ 16 →
          BitVec.ofNat 64 (ec.1 + off) ≠ BitVec.ofNat 64 (globN s "ev" + 16) := by
        intro off hoff hne16 heq_bv
        have heq := congrArg BitVec.toNat heq_bv
        rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at heq
        rw [hch_eq, List.mem_cons] at hec
        rcases hec with rfl | htail
        · dsimp only at heq; omega
        · have hFO_pw := hInv.2.choose_spec.2.2.2.2.2.2.2.1
          rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hFO_pw
          have hd := hFO_pw.2.2 (globN s "ev", 280) (by simp [frameObjects]) (ec.1, 280)
            (List.mem_flatten.2 ⟨_, List.mem_map.2 ⟨ec, htail, rfl⟩, by simp [frameObjects]⟩)
          rcases hd with h0 | h0 | h1 | h2 <;> dsimp only at * <;> omega
      exact ⟨by unfold memW; rw [hmem_p _ (hne_ec 64 (by omega) (by omega))],
             by unfold memW; rw [hmem_p _ (hne_ec 192 (by omega) (by omega))]⟩
    exact ⟨hek.1, hglob_p, hek.2.2.2, hR_eq⟩
  refine ⟨fun v hv => ?_, fun ⟨v, hv⟩ => ?_⟩
  · obtain ⟨h1, h2, h3, h4⟩ := hstep_res (Or.inl ⟨v, hv⟩)
    exact ⟨h1, h3, le_of_eq h4, h2⟩
  · obtain ⟨h1, _, h3, h4⟩ := hstep_res (Or.inr ⟨_, v, hv, by decide⟩)
    exact ⟨h1, h3, le_of_eq h4⟩

end InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
