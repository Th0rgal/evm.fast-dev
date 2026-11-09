import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group09LogReturnRevertTail
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterCutover
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.RouterChainCutover

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

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
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

local notation "evmR" => R11Shards.OpDispatchSpec.evmR

private theorem two_word_arg_lookup_ret_r29 {fname p1 p2 : MlS} {body : ProgHOL 64}
    {rsh : ShapeHOL} {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hne : p1 ≠ p2)
    (hlook : originalRuntimeCode.lookup fname = some ([(p1, .one), (p2, .one)], body, rsh))
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup fname vals = some (body', callee, ret')) :
    body' = body ∧ ret' = rsh ∧ ∃ w1 w2 : BitVec 64,
      vals = [.val (.word w1), .val (.word w2)] ∧
      callee.lookup p1 = some (.val (.word w1)) ∧
      callee.lookup p2 = some (.val (.word w2)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup fname vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | _⟩⟩
  · simp at hx
  · simp at hx
  · rcases v1 with ⟨⟨w1⟩⟩ | _ | _ <;> rcases v2 with ⟨⟨w2⟩⟩ | _ | _ <;>
      simp [shapeOfHOLExact, shapeEqHOL] at hx
    rcases hx with ⟨_, hbody_eq, hloc, hret_eq⟩
    refine ⟨hbody_eq.symm, hret_eq.symm, w1, w2, rfl, ?_, ?_⟩
    · have hfn := congrFun hloc.symm p1
      simpa [FUPDATE_LIST, FUPDATE, hne, Ne.symm hne] using hfn
    · have hfn := congrFun hloc.symm p2
      simpa [FUPDATE_LIST, FUPDATE, hne, Ne.symm hne] using hfn
  · simp at hx

private theorem eps_mul64x64_eight_exact_r29 (nw : BitVec 64) :
    EvmPreservingSpec
      (fun s =>
        s.locals.lookup (ofString "a") = some (.val (.word 8#64)) ∧
        s.locals.lookup (ofString "b") = some (.val (.word nw)))
      (fun s v post => LocFrame s post ∧
        ∃ lo hi : BitVec 64,
          v = .rStruct [.val (.word lo), .val (.word hi)] ∧
          (hi = 0#64 → lo.toNat = 8 * nw.toNat ∧ 8 * nw.toNat < 2 ^ 64))
      (ofString "mul64x64") := by
  obtain ⟨params, body, retShape, hlk, hro⟩ := eps_mul64x64
  have hlk_eq := lookup_mul64x64.symm.trans hlk
  injection hlk_eq with hp
  rcases Prod.mk.inj hp with ⟨rfl, hp2⟩
  rcases Prod.mk.inj hp2 with ⟨hbody_eq, rfl⟩
  subst hbody_eq
  refine ⟨_, _, _, lookup_mul64x64, ?_⟩
  intro F s hcode hInv ⟨ha, hb⟩ hlookup hnt
  have hs := hro s hcode hInv trivial hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨h1, h2, h3, hlf⟩ := hs.1 v hv
  obtain ⟨lo, hi, rfl, hexact⟩ := eval_mul64x64_eight_exact_g09 s ha hb v hv
  exact ⟨h1, h2, h3, hlf, lo, hi, rfl, hexact⟩

private def HandlerRunBoth {F : Type} (W : Prop) (s0 : PanSemStateFiniteExact 64 F)
    (P : PanSemStateFiniteExact 64 F → Prop) (charged : Bool)
    (prog : ProgHOL 64) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 F), t.code = originalRuntimeCode →
    EvmInv t → HeadMemAligned t → (W → Group09ChainWF.HeadMemChainWF t) →
    (evmChain t).length = (evmChain s0).length →
    (if charged then evmR t < evmR s0 else evmR t ≤ evmR s0) → P t →
    (evaluateHOLFiniteState t prog).1 ≠ some .timeOut →
    OpDispatchPostBoth W s0 (evaluateHOLFiniteState t prog).1 (evaluateHOLFiniteState t prog).2

private theorem rbound_to_le_r29 {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

private theorem rbound_step_r29 {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem HandlerRunBoth.raise_evmErr {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool} (e : ExpHOL 64) :
    HandlerRunBoth W s0 P charged (.raise (ofString "EvmErr") e) := by
  intro t _ hi _ hwf hlen hR _ _
  have hR_le := rbound_to_le_r29 hR
  rw [evaluateHOLFiniteState_raise]
  split
  · dsimp only
    split
    · have hi' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hi
      have hwf' : W → Group09ChainWF.HeadMemChainWF (emptyLocalsHOLFinite t) :=
        fun hw => Group09ChainWF.headMemChainWF_locals t (emptyLocalsHOLFinite t).locals t.clock (hwf hw)
      have hc_el := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      have hR_el : evmR (emptyLocalsHOLFinite t) ≤ evmR s0 := by
        have h_eq : evmR (emptyLocalsHOLFinite t) = evmR t := hc_el.2.1
        omega
      refine ⟨⟨?_, fun _ => ⟨hi', by rw [hc_el.2.2.1]; exact hlen, hR_el⟩⟩,
        fun hw => ⟨?_, fun _ => ⟨⟨hi', hwf' hw⟩, by rw [hc_el.2.2.1]; exact hlen, hR_el⟩⟩⟩
      · rintro ⟨_, h⟩; cases h
      · rintro ⟨_, h⟩; cases h
    · exact opDispatchPostBoth_error W s0 t
  · exact opDispatchPostBoth_error W s0 t

private theorem HandlerRunBoth.seq_ite_raise_skip {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool} {cond errExp : ExpHOL 64} {cont : ProgHOL 64}
    (hcont : HandlerRunBoth W s0 P charged cont) :
    HandlerRunBoth W s0 P charged
      (.seq (.ite cond (.raise (ofString "EvmErr") errExp) .skip) cont) := by
  intro t hc hi hhm hwf hlen hR hp hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w _
    by_cases hz : w = 0
    · subst hz; simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      intro hnt; exact hcont t hc hi hhm hwf hlen hR hp hnt
    · simp only [hz, ↓reduceIte]
      rcases hraise : evaluateHOLFiniteState t (.raise (ofString "EvmErr") errExp) with ⟨rr, sr⟩
      cases rr with
      | none => exact absurd hraise (fun h => raise_ne_none t _ errExp (by rw [h]))
      | some r0 =>
        dsimp only; intro hnt
        have hr := (HandlerRunBoth.raise_evmErr (W := W) (P := P) (charged := charged) errExp)
          t hc hi hhm hwf hlen hR hp (by rw [hraise]; exact hnt)
        rw [hraise] at hr; exact hr
  · intro _; dsimp only; exact opDispatchPostBoth_error W s0 t

private theorem HandlerRunBoth.seq_assign_local {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool} {nm : MlS} {exp : ExpHOL 64} {cont : ProgHOL 64}
    (hasgn : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) exp = some v →
      P t → Q (setKvarHOLFinite .local nm v t))
    (hcont : HandlerRunBoth W s0 Q charged cont) :
    HandlerRunBoth W s0 P charged (.seq (.assign .local nm exp) cont) := by
  intro t hc hi hhm hwf hlen hR hp hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_assign] at hnt ⊢
  revert hnt
  split
  · intro _; exact opDispatchPostBoth_error W s0 t
  · rename_i v hv
    split
    · dsimp only; intro hnt
      let t1 := setKvarHOLFinite .local nm v t
      have hi1 : EvmInv t1 := localsFree_evmInv t t1.locals t.clock hi
      have hhm1 : HeadMemAligned t1 := headMemAligned_congr_head rfl (fun _ _ => rfl) hhm
      have hwf1 : W → Group09ChainWF.HeadMemChainWF t1 :=
        fun hw => Group09ChainWF.headMemChainWF_locals t t1.locals t.clock (hwf hw)
      have hc1 := evm_congr (s := t) (t := t1) rfl rfl
      have hR1 : if charged then evmR t1 < evmR s0 else evmR t1 ≤ evmR s0 := by
        have h_eq : evmR t1 = evmR t := hc1.2.1
        rw [h_eq]; exact hR
      exact hcont t1 hc hi1 hhm1 hwf1 (hc1.2.2.1.trans hlen) hR1 (hasgn t v hv hp) hnt
    · intro _; exact opDispatchPostBoth_error W s0 t

private theorem HandlerRunBoth.seq_ite_unit {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool} {cond : ExpHOL 64} {yes no cont : ProgHOL 64}
    (hyes : ∀ (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word w)) →
      w ≠ 0 →
      HandlerRunBoth W s0 P charged (.seq yes cont))
    (hno : ∀ (t : PanSemStateFiniteExact 64 F),
      P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cond = some (.val (.word 0)) →
      HandlerRunBoth W s0 P charged (.seq no cont)) :
    HandlerRunBoth W s0 P charged (.seq (.ite cond yes no) cont) := by
  intro t hc hi hhm hwf hlen hR hp hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i w hcond
    by_cases hw0 : w = 0
    · subst hw0; simp only [↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hno t hp hcond t hc hi hhm hwf hlen hR hp hnt
    · simp only [hw0, ↓reduceIte]
      rw [← evaluateHOLFiniteState_seq_line780]
      intro hnt; exact hyes t w hp hcond hw0 t hc hi hhm hwf hlen hR hp hnt
  · intro _; dsimp only; exact opDispatchPostBoth_error W s0 t

private theorem HandlerRunBoth.decCall_stack_pop {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool} {nm : MlS} {cont : ProgHOL 64}
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
      (cpost : PanSemStateFiniteExact 64 F),
      P t →
      shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRunBoth W s0 Q charged cont) :
    HandlerRunBoth W s0 P charged
      (.decCall nm (.comb [.one, .one, .one, .one]) (ofString "stack_pop") [] cont) := by
  intro t hc hi hhm hwf hlen hR hp hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := eps_stack_pop_headMem
  obtain ⟨paramsA, bodyA, retA, hlookA, hspecA⟩ := Group09ChainWF.epsA_stack_pop
  have hlk_eq := hlook.symm.trans hlookA
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨rfl, rfl⟩
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [] with _ | values
  · exact opDispatchPostBoth_error W s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "stack_pop") values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostBoth_error W s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hbody_eq : body' = body :=
          lookupCodeHOLFinite_installed_body t.code.lookup (ofString "stack_pop") params body body'
            retShape ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = retShape := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup (ofString "stack_pop") values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hhm_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
          headMemAligned_congr_head rfl (fun _ _ => rfl) hhm
        have hwf_ce : W → Group09ChainWF.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          fun hw => Group09ChainWF.headMemChainWF_locals t callee (t.clock - 1) (hwf hw)
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "stack_pop") values =
            some (body, callee, retShape) := by rwa [← hc]
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        cases res with
        | none => exact opDispatchPostBoth_error W s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              have hsh_v : shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true := by
                simp only [Bool.and_eq_true] at hsh_ok; exact hsh_ok.1
              have hs1 := hspec (callEntryStateHOLFinite t callee) hc hi_ce trivial ⟨values, hl_orig⟩
                (by rw [hrun]; simp)
              rw [hrun] at hs1; dsimp only at hs1
              obtain ⟨hi_cp, hch_cp, hR_cp, _, hhm_imp⟩ := hs1.1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hi_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hi_cp
              have hhm_res : HeadMemAligned resumed :=
                headMemAligned_congr_head rfl (fun _ _ => rfl) (hhm_imp hhm_ce)
              have hwf_res : W → Group09ChainWF.HeadMemChainWF resumed := fun hw => by
                have hsA := hspecA (callEntryStateHOLFinite t callee) hc hi_ce (hwf_ce hw) trivial ⟨values, hl_orig⟩
                  (by rw [hrun]; simp)
                rw [hrun] at hsA; dsimp only at hsA
                exact Group09ChainWF.headMemChainWF_locals cpost resumed.locals cpost.clock (hsA.1 v rfl).1.2
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rbound_step_r29 (by
                  have h1 : evmR resumed = evmR cpost := hc_res.2.1
                  have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                  omega) hR
              have hb := hcont resumed (hmeta.trans hc) hi_res hhm_res hwf_res hlen_res hR_res
                (hstep t v cpost hp hsh_v) (by simpa [resumed] using hnt)
              exact opDispatchPostBoth_congr_lc rfl hb
            · exact opDispatchPostBoth_error W s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              have hs1 := hspec (callEntryStateHOLFinite t callee) hc hi_ce trivial ⟨values, hl_orig⟩
                (by rw [hrun]; simp)
              rw [hrun] at hs1; dsimp only at hs1
              obtain ⟨hi_cp, hch_cp, hR_cp⟩ := hs1.2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hlen_el : (evmChain cpost.emptyLocalsHOLFinite).length = (evmChain s0).length := by
                rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_el : evmR cpost.emptyLocalsHOLFinite ≤ evmR s0 := by
                have := rbound_to_le_r29 hR
                have h1 : evmR cpost.emptyLocalsHOLFinite = evmR cpost := hc_el.2.1
                have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                omega
              have hnot_ret : ∀ w, some (PanSemResultExact.exception (ofString "EvmErr") ev) ≠
                  some (.returned w) := fun _ h => by cases h
              refine ⟨⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨hi_el, hlen_el, hR_el⟩⟩, fun hw => ?_⟩
              have hsA := hspecA (callEntryStateHOLFinite t callee) hc hi_ce (hwf_ce hw) trivial ⟨values, hl_orig⟩
                (by rw [hrun]; simp)
              rw [hrun] at hsA; dsimp only at hsA
              have hw_el : Group09ChainWF.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group09ChainWF.headMemChainWF_locals cpost _ cpost.clock (hsA.2 ⟨ev, rfl⟩).1.2
              exact ⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨⟨hi_el, hw_el⟩, hlen_el, hR_el⟩⟩
            · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostBoth_error W s0 cpost
          | «continue» => exact opDispatchPostBoth_error W s0 cpost
          | finalFfi _ =>
            refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostBoth_error W s0 cpost.emptyLocalsHOLFinite

private theorem HandlerRunBoth.decCall_ro {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qr : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → Prop}
    {charged : Bool} {nm : MlS} {sh : ShapeHOL} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hro_fn : opRoCallees fname = true)
    (hf : EvmPreservingSpec Pc (fun s v post => LocFrame s post ∧ Qr s v) fname)
    (hentry : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body' : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL),
      t.code = originalRuntimeCode → EvmInv t → HeadMemAligned t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (retShape : ShapeHOL) (v : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      EvmInv t → HeadMemAligned t → P t →
      shapeEqHOL (shapeOfHOLExact v) sh = true →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      LocFrame (callEntryStateHOLFinite t callee) cpost →
      Qr (callEntryStateHOLFinite t callee) v →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRunBoth W s0 Q charged cont) :
    HandlerRunBoth W s0 P charged (.decCall nm sh fname args cont) := by
  intro t hc hi hhm hwf hlen hR hp hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact opDispatchPostBoth_error W s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPostBoth_error W s0 t
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
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hwf_ce : W → Group09ChainWF.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          fun hw => Group09ChainWF.headMemChainWF_locals t callee (t.clock - 1) (hwf hw)
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hi hhm hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hro_body := opRoCallees_good fname hro_fn values body callee retShape hl_orig
        have hsafe_ro := evaluate_readOnlyProg opRoCallees opRoCallees_good body hro_body
          (callEntryStateHOLFinite t callee) hc
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        cases res with
        | none => exact opDispatchPostBoth_error W s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            split
            · rename_i hsh_ok
              rw [if_pos hsh_ok] at hnt
              have hsh_v : shapeEqHOL (shapeOfHOLExact v) sh = true := by
                simp only [Bool.and_eq_true] at hsh_ok; exact hsh_ok.1
              have hs1 := hspec (callEntryStateHOLFinite t callee) hc hi_ce hPc ⟨values, hl_orig⟩
                (by rw [hrun]; simp)
              rw [hrun] at hs1; dsimp only at hs1
              obtain ⟨hi_cp, hch_cp, hR_cp, hlf, hQr⟩ := hs1.1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hm_cp : cpost.memory = t.memory :=
                show cpost.memory = (callEntryStateHOLFinite t callee).memory by rw [hlf]
              have hg_cp : cpost.globals = t.globals :=
                show cpost.globals = (callEntryStateHOLFinite t callee).globals by rw [hlf]
              have hi_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hi_cp
              have hhm_res : HeadMemAligned resumed :=
                headMemAligned_congr_head hg_cp
                  (fun _ _ => by dsimp only [resumed, setVarHOLFinite]; unfold memW; rw [hm_cp]) hhm
              have hwf_res : W → Group09ChainWF.HeadMemChainWF resumed := fun hw =>
                Group09ChainWF.headMemChainWF_locals cpost resumed.locals cpost.clock
                  (Group09ChainWF.headMemChainWF_of_locFrame (hwf_ce hw) hlf)
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rbound_step_r29 (by
                  have h1 : evmR resumed = evmR cpost := hc_res.2.1
                  have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                  omega) hR
              have hb := hcont resumed (hmeta.trans hc) hi_res hhm_res hwf_res hlen_res hR_res
                (hstep t values body callee retShape v cpost hi hhm hp hsh_v hargs hl_orig hlf hQr)
                (by simpa [resumed] using hnt)
              exact opDispatchPostBoth_congr_lc rfl hb
            · exact opDispatchPostBoth_error W s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              have hs1 := hspec (callEntryStateHOLFinite t callee) hc hi_ce hPc ⟨values, hl_orig⟩
                (by rw [hrun]; simp)
              rw [hrun] at hs1; dsimp only at hs1
              obtain ⟨hi_cp, hch_cp, hR_cp⟩ := hs1.2 ⟨ev, rfl⟩
              have hlf_cp : LocFrame (callEntryStateHOLFinite t callee) cpost := by
                have hres := hsafe_ro.to_resumes (by rw [hrun]; exact Or.inr ⟨_, ev, rfl, by decide⟩)
                simpa [hrun] using hres
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hlen_el : (evmChain cpost.emptyLocalsHOLFinite).length = (evmChain s0).length := by
                rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_el : evmR cpost.emptyLocalsHOLFinite ≤ evmR s0 := by
                have := rbound_to_le_r29 hR
                have h1 : evmR cpost.emptyLocalsHOLFinite = evmR cpost := hc_el.2.1
                have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                omega
              have hnot_ret : ∀ w, some (PanSemResultExact.exception (ofString "EvmErr") ev) ≠
                  some (.returned w) := fun _ h => by cases h
              refine ⟨⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨hi_el, hlen_el, hR_el⟩⟩, fun hw => ?_⟩
              have hw_el : Group09ChainWF.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group09ChainWF.headMemChainWF_locals cpost _ cpost.clock
                  (Group09ChainWF.headMemChainWF_of_locFrame (hwf_ce hw) hlf_cp)
              exact ⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨⟨hi_el, hw_el⟩, hlen_el, hR_el⟩⟩
            · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPostBoth_error W s0 cpost
          | «continue» => exact opDispatchPostBoth_error W s0 cpost
          | finalFfi _ =>
            refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPostBoth_error W s0 cpost.emptyLocalsHOLFinite

private theorem HandlerRunBoth.seq_call_assign_local_ro {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {Pc : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Qr : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → Prop}
    {charged : Bool} {nm : MlS} {fname : MlS}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hro_fn : opRoCallees fname = true)
    (hf : EvmPreservingSpec Pc (fun s v post => LocFrame s post ∧ Qr s v) fname)
    (hentry : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body' : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (ret' : ShapeHOL),
      t.code = originalRuntimeCode → EvmInv t → HeadMemAligned t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite t.code.lookup fname values = some (body', callee, ret') →
      Pc (callEntryStateHOLFinite t callee))
    (hstep : ∀ (t : PanSemStateFiniteExact 64 F) (values : List (ValueHOL 64))
      (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
      (retShape : ShapeHOL) (v : ValueHOL 64) (cpost : PanSemStateFiniteExact 64 F),
      EvmInv t → HeadMemAligned t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, retShape) →
      LocFrame (callEntryStateHOLFinite t callee) cpost →
      Qr (callEntryStateHOLFinite t callee) v →
      Q (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRunBoth W s0 Q charged cont) :
    HandlerRunBoth W s0 P charged (.seq (.call (some (some (.local, nm), none)) fname args) cont) := by
  intro t hc hi hhm hwf hlen hR hp hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · dsimp only; exact opDispatchPostBoth_error W s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · dsimp only; exact opDispatchPostBoth_error W s0 t
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
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hwf_ce : W → Group09ChainWF.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          fun hw => Group09ChainWF.headMemChainWF_locals t callee (t.clock - 1) (hwf hw)
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values body callee retShape hc hi hhm hp hargs hl
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, retShape) := by rwa [← hc]
        have hro_body := opRoCallees_good fname hro_fn values body callee retShape hl_orig
        have hsafe_ro := evaluate_readOnlyProg opRoCallees opRoCallees_good body hro_body
          (callEntryStateHOLFinite t callee) hc
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        cases res with
        | none => dsimp only; exact opDispatchPostBoth_error W s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) retShape = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              by_cases hvld : isValidValueHOLExact t.toExact .local nm v = true
              · simp only [hvld, ↓reduceIte] at hnt ⊢
                dsimp only [setKvarHOLFinite] at hnt ⊢
                have hs1 := hspec (callEntryStateHOLFinite t callee) hc hi_ce hPc ⟨values, hl_orig⟩
                  (by rw [hrun]; simp)
                rw [hrun] at hs1; dsimp only at hs1
                obtain ⟨hi_cp, hch_cp, hR_cp, hlf, hQr⟩ := hs1.1 v rfl
                let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
                have hm_cp : cpost.memory = t.memory :=
                  show cpost.memory = (callEntryStateHOLFinite t callee).memory by rw [hlf]
                have hg_cp : cpost.globals = t.globals :=
                  show cpost.globals = (callEntryStateHOLFinite t callee).globals by rw [hlf]
                have hi_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hi_cp
                have hhm_res : HeadMemAligned resumed :=
                  headMemAligned_congr_head hg_cp
                    (fun _ _ => by dsimp only [resumed, setVarHOLFinite]; unfold memW; rw [hm_cp]) hhm
                have hwf_res : W → Group09ChainWF.HeadMemChainWF resumed := fun hw =>
                  Group09ChainWF.headMemChainWF_locals cpost resumed.locals cpost.clock
                    (Group09ChainWF.headMemChainWF_of_locFrame (hwf_ce hw) hlf)
                have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
                have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                  rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
                have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                  rbound_step_r29 (by
                    have h1 : evmR resumed = evmR cpost := hc_res.2.1
                    have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                    omega) hR
                exact hcont resumed (hmeta.trans hc) hi_res hhm_res hwf_res hlen_res hR_res
                  (hstep t values body callee retShape v cpost hi hhm hp hargs hl_orig hlf hQr)
                  (by simpa [resumed] using hnt)
              · simp only [hvld, Bool.false_eq_true, ↓reduceIte]
                exact opDispatchPostBoth_error W s0 cpost
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostBoth_error W s0 cpost
          | exception eid ev =>
            dsimp only at hnt ⊢
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              have hs1 := hspec (callEntryStateHOLFinite t callee) hc hi_ce hPc ⟨values, hl_orig⟩
                (by rw [hrun]; simp)
              rw [hrun] at hs1; dsimp only at hs1
              obtain ⟨hi_cp, hch_cp, hR_cp⟩ := hs1.2 ⟨ev, rfl⟩
              have hlf_cp : LocFrame (callEntryStateHOLFinite t callee) cpost := by
                have hres := hsafe_ro.to_resumes (by rw [hrun]; exact Or.inr ⟨_, ev, rfl, by decide⟩)
                simpa [hrun] using hres
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hi_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hlen_el : (evmChain cpost.emptyLocalsHOLFinite).length = (evmChain s0).length := by
                rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_el : evmR cpost.emptyLocalsHOLFinite ≤ evmR s0 := by
                have := rbound_to_le_r29 hR
                have h1 : evmR cpost.emptyLocalsHOLFinite = evmR cpost := hc_el.2.1
                have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                omega
              have hnot_ret : ∀ w, some (PanSemResultExact.exception (ofString "EvmErr") ev) ≠
                  some (.returned w) := fun _ h => by cases h
              refine ⟨⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨hi_el, hlen_el, hR_el⟩⟩, fun hw => ?_⟩
              have hw_el : Group09ChainWF.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group09ChainWF.headMemChainWF_locals cpost _ cpost.clock
                  (Group09ChainWF.headMemChainWF_of_locFrame (hwf_ce hw) hlf_cp)
              exact ⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨⟨hi_el, hw_el⟩, hlen_el, hR_el⟩⟩
            · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => dsimp only; exact opDispatchPostBoth_error W s0 cpost
          | «continue» => dsimp only; exact opDispatchPostBoth_error W s0 cpost
          | finalFfi _ =>
            dsimp only
            refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => dsimp only; exact opDispatchPostBoth_error W s0 cpost.emptyLocalsHOLFinite

private theorem HandlerRunBoth.seq_charge_gas_exact {F : Type} {W : Prop}
    {s0 : PanSemStateFiniteExact 64 F} {P Q : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool} {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ (t : PanSemStateFiniteExact 64 F) (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      P t → 0 < w.toNat)
    (hstep : ∀ (t cpost : PanSemStateFiniteExact 64 F) (amtw : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word amtw)) →
      amtw.toNat < 2 ^ 64 - 1 →
      EvmInv t → HeadMemAligned t → P t →
      EvmInv cpost → cpost.globals = t.globals → evmChain cpost = evmChain t →
      (∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
        memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off)) →
      Q { cpost with locals := t.locals })
    (hcont : HandlerRunBoth W s0 Q true cont) :
    HandlerRunBoth W s0 P charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hi hhm hwf hlen hR hp hnt
  have hR_le := rbound_to_le_r29 hR
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · dsimp only; exact opDispatchPostBoth_error W s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · dsimp only; exact opDispatchPostBoth_error W s0 t
    · simp only [hl] at hnt ⊢
      by_cases hz : t.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hv_list : ∃ v0, @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
            some v0 ∧ values = [v0] := by
          rw [evalListHOLFinite_eq_toExact] at hargs
          simp only [evalListHOLExact] at hargs
          rcases he : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp with _ | v0
          · simp [he] at hargs
          · simp only [he, Option.some.injEq] at hargs; exact ⟨v0, rfl, hargs.symm⟩
        obtain ⟨v0, hv0_ev, rfl⟩ := hv_list
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_gas") [v0] =
            some (body', callee, ret') := by rwa [← hc]
        obtain ⟨rfl, rfl, amtw, rfl, hamt_cal⟩ := one_word_arg_lookup M21.lookup_charge_gas hl_orig
        have hamt_pos : 0 < amtw.toNat := hpos t amtw hv0_ev hp
        have hi_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hi
        have hwf_ce : W → Group09ChainWF.HeadMemChainWF (callEntryStateHOLFinite t callee) :=
          fun hw => Group09ChainWF.headMemChainWF_locals t callee (t.clock - 1) (hwf hw)
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata
          (callEntryStateHOLFinite t callee) (sourceFnBody Guest.Software.guestFn_charge_gas)).1
        have hcg := charge_gas_body_exact (callEntryStateHOLFinite t callee) hi_ce hamt_cal
        have hcg_m := eps_charge_gas_any_headMem
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee)
          (sourceFnBody Guest.Software.guestFn_charge_gas) with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta hcg ⊢
        change cpost.code = t.code at hmeta
        cases res with
        | none => dsimp only; exact opDispatchPostBoth_error W s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            dsimp only at hnt ⊢
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hi_cp, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              have hamt_lt : amtw.toNat < 2 ^ 64 - 1 :=
                charge_gas_return_amount_lt_g09 (callEntryStateHOLFinite t callee) hi_ce hamt_cal (by rw [hrun])
              have hmem_cp : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
                  memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off) := by
                obtain ⟨p_m, b_m, r_m, hlk_m, hsp_m⟩ := hcg_m
                have heq_m := M21.lookup_charge_gas.symm.trans hlk_m
                injection heq_m with hp_m
                rcases Prod.mk.inj hp_m with ⟨rfl, hp_m2⟩
                rcases Prod.mk.inj hp_m2 with ⟨hb_eq, rfl⟩
                subst hb_eq
                have hs_m := hsp_m (callEntryStateHOLFinite t callee) hc hi_ce trivial
                  ⟨[.val (.word amtw)], hl_orig⟩ (by rw [hrun]; simp)
                rw [hrun] at hs_m; dsimp only at hs_m
                exact (hs_m.1 v rfl).2.2.2.2
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hi_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hi_cp
              have hhm_cp : HeadMemAligned cpost := headMemAligned_congr_head hglob_cp hmem_cp hhm
              have hhm_res : HeadMemAligned resumed := headMemAligned_congr_head rfl (fun _ _ => rfl) hhm_cp
              have hwf_res : W → Group09ChainWF.HeadMemChainWF resumed := fun hw => by
                have hcgA := Group09ChainWF.charge_gas_body_exactA_g09
                  (callEntryStateHOLFinite t callee) hi_ce (hwf_ce hw) hamt_cal
                rw [hrun] at hcgA; dsimp only at hcgA
                exact Group09ChainWF.headMemChainWF_locals cpost t.locals cpost.clock (hcgA.1 v rfl).1.2
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : evmR resumed < evmR s0 := by
                have h1 : evmR resumed = evmR cpost := hc_res.2.1
                have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                omega
              exact hcont resumed (hmeta.trans hc) hi_res hhm_res hwf_res hlen_res (by simp [hR_lt])
                (hstep t cpost amtw hv0_ev hamt_lt hi hhm hp hi_cp hglob_cp
                  (hch_cp.trans (evmChain_congr rfl rfl)) hmem_cp)
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPostBoth_error W s0 cpost
          | exception eid ev =>
            dsimp only at hnt ⊢
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hi_cp, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hi_el : EvmInv cpost.emptyLocalsHOLFinite := localsFree_evmInv cpost _ cpost.clock hi_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hlen_el : (evmChain cpost.emptyLocalsHOLFinite).length = (evmChain s0).length := by
                rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_el : evmR cpost.emptyLocalsHOLFinite ≤ evmR s0 := by
                have h1 : evmR cpost.emptyLocalsHOLFinite = evmR cpost := hc_el.2.1
                have h2 : evmR (callEntryStateHOLFinite t callee) = evmR t := hc_ce.2.1
                omega
              have hnot_ret : ∀ w, some (PanSemResultExact.exception (ofString "EvmErr") ev) ≠
                  some (.returned w) := fun _ h => by cases h
              refine ⟨⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨hi_el, hlen_el, hR_el⟩⟩, fun hw => ?_⟩
              have hcgA := Group09ChainWF.charge_gas_body_exactA_g09
                (callEntryStateHOLFinite t callee) hi_ce (hwf_ce hw) hamt_cal
              rw [hrun] at hcgA; dsimp only at hcgA
              have hw_el : Group09ChainWF.HeadMemChainWF cpost.emptyLocalsHOLFinite :=
                Group09ChainWF.headMemChainWF_locals cpost _ cpost.clock (hcgA.2 ⟨ev, rfl⟩).1.2
              exact ⟨fun ⟨w, hw⟩ => (hnot_ret w hw).elim, fun _ => ⟨⟨hi_el, hw_el⟩, hlen_el, hR_el⟩⟩
            · refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => dsimp only; exact opDispatchPostBoth_error W s0 cpost
          | «continue» => dsimp only; exact opDispatchPostBoth_error W s0 cpost
          | finalFfi _ =>
            dsimp only
            refine opDispatchPostBoth_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => dsimp only; exact opDispatchPostBoth_error W s0 cpost.emptyLocalsHOLFinite

private theorem op_log_body_both_r29 {F : Type}
    {W : Prop} (s0 : PanSemStateFiniteExact 64 F) {nt : BitVec 64}
    (hc0 : s0.code = originalRuntimeCode) (hInv0 : EvmInv s0)
    (hHM0 : HeadMemAligned s0) (hWF0 : W → Group09ChainWF.HeadMemChainWF s0)
    (hnt0 : s0.locals.lookup (ofString "ntopics") = some (.val (.word nt)))
    (hnt4 : nt.toNat ≤ 4)
    (hnt_prog : (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_op_log)).1 ≠
      some .timeOut) :
    OpDispatchPostBoth W s0
      (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_op_log)).1
      (evaluateHOLFiniteState s0 (sourceFnBody Guest.Software.guestFn_op_log)).2 := by
  have hbody_eq : sourceFnBody Guest.Software.guestFn_op_log =
      .decCall (ofString "start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.seq
            (.ite (.cmp .lower
                (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
                (.var .local (ofString "ntopics")))
              (.raise (ofString "EvmErr") (.const 2#64))
              .skip)
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
                [.var .local (ofString "start"), .var .local (ofString "size")]
                (.decCall (ofString "dc") (.comb [.one, .one]) (ofString "mul64x64")
                  [.const 8#64, .var .local (ofString "n")]
                  (.decCall (ofString "cost") .one (ofString "add_sat")
                    [.op .add [.const 375#64, .panop .mul [.const 375#64, .var .local (ofString "ntopics")]],
                     .rfield 0 (.var .local (ofString "x"))]
                    (.seq
                      (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "dc"))) (.const 0#64))
                        (.assign .local (ofString "cost") (.const 18446744073709551615#64))
                        (.call (some (some (.local, ofString "cost"), none)) (ofString "add_sat")
                          [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))]))
                      (.seq
                        (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")])
                        opLogPostChargeProg)))))))) := rfl
  rw [hbody_eq] at hnt_prog ⊢
  suffices hrun : HandlerRunBoth W s0
      (fun t => t.locals.lookup (ofString "ntopics") = some (.val (.word nt))) false
      (.decCall (ofString "start") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
        (.decCall (ofString "size") (.comb [.one, .one, .one, .one]) (ofString "stack_pop") []
          (.seq
            (.ite (.cmp .lower
                (.load .one (.op .add [.var .global (ofString "ev"), .const 16#64]))
                (.var .local (ofString "ntopics")))
              (.raise (ofString "EvmErr") (.const 2#64))
              .skip)
            (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
              (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
                [.var .local (ofString "start"), .var .local (ofString "size")]
                (.decCall (ofString "dc") (.comb [.one, .one]) (ofString "mul64x64")
                  [.const 8#64, .var .local (ofString "n")]
                  (.decCall (ofString "cost") .one (ofString "add_sat")
                    [.op .add [.const 375#64, .panop .mul [.const 375#64, .var .local (ofString "ntopics")]],
                     .rfield 0 (.var .local (ofString "x"))]
                    (.seq
                      (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "dc"))) (.const 0#64))
                        (.assign .local (ofString "cost") (.const 18446744073709551615#64))
                        (.call (some (some (.local, ofString "cost"), none)) (ofString "add_sat")
                          [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))]))
                      (.seq
                        (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")])
                        opLogPostChargeProg))))))))) by
    exact hrun s0 hc0 hInv0 hHM0 hWF0 rfl (by simp) hnt0 hnt_prog
  -- Step 1: start := stack_pop()
  apply HandlerRunBoth.decCall_stack_pop (Q := fun t =>
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
    ∃ sa sb sc sd : BitVec 64,
      t.locals.lookup (ofString "start") =
        some (.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]))
  · intro t v cpost hnt_lk hsh
    obtain ⟨sa, sb, sc, sd, rfl⟩ := shapeEq_comb4_iff v hsh
    refine ⟨?_, sa, sb, sc, sd, ?_⟩
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "start" ≠ ofString "ntopics")] using hnt_lk
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Step 2: size := stack_pop()
  apply HandlerRunBoth.decCall_stack_pop (Q := fun t =>
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
    ∃ sa sb sc sd za zb zc zd : BitVec 64,
      t.locals.lookup (ofString "start") =
        some (.rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]) ∧
      t.locals.lookup (ofString "size") =
        some (.rStruct [.val (.word za), .val (.word zb), .val (.word zc), .val (.word zd)]))
  · intro t v cpost ⟨hnt_lk, sa, sb, sc, sd, hstart_lk⟩ hsh
    obtain ⟨za, zb, zc, zd, rfl⟩ := shapeEq_comb4_iff v hsh
    refine ⟨?_, sa, sb, sc, sd, za, zb, zc, zd, ?_, ?_⟩
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "size" ≠ ofString "ntopics")] using hnt_lk
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "size" ≠ ofString "start")] using hstart_lk
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Step 3: if sp < ntopics raise EvmErr 2
  apply HandlerRunBoth.seq_ite_raise_skip
  -- Unpack existential parameters before Step 4
  intro t3 hc3 hi3 hhm3 hwf3 hlen3 hR3 ⟨hnt_lk3, sa, sb, sc, sd, za, zb, zc, zd, hstart_lk3, hsize_lk3⟩ hnt3
  let startVal : ValueHOL 64 := .rStruct [.val (.word sa), .val (.word sb), .val (.word sc), .val (.word sd)]
  let sizeVal : ValueHOL 64 := .rStruct [.val (.word za), .val (.word zb), .val (.word zc), .val (.word zd)]
  let nw : BitVec 64 := satWordG09 sizeVal
  have hlk_sat_word : originalRuntimeCode.lookup (ofString "sat_word") =
      some ([(ofString "v", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_sat_word, .one) :=
    lookup_of_guestAst_getElem 440 (by rw [guestAst_len]; decide)
      (extractFn Guest.Software.guestFn_sat_word) rfl
  suffices hstep4 : HandlerRunBoth W s0
      (fun t =>
        t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
        t.locals.lookup (ofString "start") = some startVal ∧
        t.locals.lookup (ofString "size") = some sizeVal) false
      (.decCall (ofString "n") .one (ofString "sat_word") [.var .local (ofString "size")]
        (.decCall (ofString "x") (.comb [.one, .one]) (ofString "extend_memory_cost1")
          [.var .local (ofString "start"), .var .local (ofString "size")]
          (.decCall (ofString "dc") (.comb [.one, .one]) (ofString "mul64x64")
            [.const 8#64, .var .local (ofString "n")]
            (.decCall (ofString "cost") .one (ofString "add_sat")
              [.op .add [.const 375#64, .panop .mul [.const 375#64, .var .local (ofString "ntopics")]],
               .rfield 0 (.var .local (ofString "x"))]
              (.seq
                (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "dc"))) (.const 0#64))
                  (.assign .local (ofString "cost") (.const 18446744073709551615#64))
                  (.call (some (some (.local, ofString "cost"), none)) (ofString "add_sat")
                    [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))]))
                (.seq
                  (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")])
                  opLogPostChargeProg)))))) by
    exact hstep4 t3 hc3 hi3 hhm3 hwf3 hlen3 hR3 ⟨hnt_lk3, hstart_lk3, hsize_lk3⟩ hnt3
  -- Step 4: n := sat_word(size)
  apply HandlerRunBoth.decCall_ro (Q := fun t =>
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
    t.locals.lookup (ofString "start") = some startVal ∧
    t.locals.lookup (ofString "size") = some sizeVal ∧
    t.locals.lookup (ofString "n") = some (.val (.word nw)))
    (by decide) eps_sat_word_exact_g09
  · intro t values body' callee ret' hc _ _ ⟨_, _, hz⟩ hargs hl
    have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "size")] = some [sizeVal] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hz]
    rw [hev] at hargs; injection hargs with hvs; subst hvs
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "sat_word") [sizeVal] =
        some (body', callee, ret') := by rwa [← hc]
    exact ⟨za, zb, zc, zd, (one_u256_arg_lookup_g09 hlk_sat_word hl_orig).2.2⟩
  · intro t values body callee retShape v cpost _ _ ⟨hnt_lk, hs, hz⟩ _ hargs hl _ hQr
    have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.var .local (ofString "size")] = some [sizeVal] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hz]
    rw [hev] at hargs; injection hargs with hvs; subst hvs
    have hv_eq := hQr sizeVal (one_u256_arg_lookup_g09 hlk_sat_word hl).2.2
    subst hv_eq
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "n" ≠ ofString "ntopics")] using hnt_lk
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "n" ≠ ofString "start")] using hs
    · simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "n" ≠ ofString "size")] using hz
    · simp [nw, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Step 5: x := extend_memory_cost1(start, size)
  apply HandlerRunBoth.decCall_ro (Q := fun t =>
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
    t.locals.lookup (ofString "start") = some startVal ∧
    t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    ∃ cw ebw : BitVec 64,
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      (ebw = 0#64 ∨ (ebw.toNat % 32 = 0 ∧ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37)))
    (by decide) eps_extend_memory_cost1_bounds
  · intros; trivial
  · intro t values body callee retShape v cpost _ hhm ⟨hnt_lk, hs, _, hn⟩ _ _ _ hlf ⟨cw, ebw, hv, heb⟩
    subst hv
    let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)])
      { cpost with locals := t.locals }
    have hm_cp : cpost.memory = t.memory := show cpost.memory = (callEntryStateHOLFinite t callee).memory by rw [hlf]
    have hg_cp : cpost.globals = t.globals := show cpost.globals = (callEntryStateHOLFinite t callee).globals by rw [hlf]
    have hm32_res : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
      have hg_ev : globN res "ev" = globN t "ev" := globN_congr hg_cp ▸ rfl
      rw [hg_ev]; dsimp only [res, setVarHOLFinite]; unfold memW; rw [hm_cp]
    have hm32_ce : memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 32) =
        memW t (globN t "ev" + 32) := rfl
    refine ⟨?_, ?_, ?_, cw, ebw, ?_, ?_⟩
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "x" ≠ ofString "ntopics")] using hnt_lk
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "x" ≠ ofString "start")] using hs
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "x" ≠ ofString "n")] using hn
    · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · rcases heb with rfl | ⟨before, after, haft_lt, haft_32, hlt_ba, heb_sub, hbef_eq⟩
      · exact Or.inl rfl
      · right
        have hbef : before = memW t (globN t "ev" + 32) := by
          rw [hm32_ce] at hbef_eq
          exact hbef_eq hhm.1
        have ha_eq : memW t (globN t "ev" + 32) + ebw.toNat = after := by omega
        have h32 : ebw.toNat % 32 = 0 := by
          have hm0 := hhm.1
          omega
        rw [hm32_res]
        exact ⟨h32, by omega⟩
  -- Step 6: dc := mul64x64(8, n)
  apply HandlerRunBoth.decCall_ro (Q := fun t =>
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
    t.locals.lookup (ofString "start") = some startVal ∧
    t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    ∃ cw ebw lo hi : BitVec 64,
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      (ebw = 0#64 ∨ (ebw.toNat % 32 = 0 ∧ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37)) ∧
      t.locals.lookup (ofString "dc") = some (.rStruct [.val (.word lo), .val (.word hi)]) ∧
      (hi = 0#64 → lo.toNat = 8 * nw.toNat ∧ 8 * nw.toNat < 2 ^ 64))
    (by decide) (eps_mul64x64_eight_exact_r29 nw)
  · intro t values body' callee ret' hc _ _ ⟨_, _, hn, _⟩ hargs hl
    have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.const 8#64, .var .local (ofString "n")] = some [.val (.word 8#64), .val (.word nw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hn]
    rw [hev] at hargs; injection hargs with hvs; subst hvs
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "mul64x64")
        [.val (.word 8#64), .val (.word nw)] = some (body', callee, ret') := by rwa [← hc]
    obtain ⟨_, _, w1, w2, heq, hw1, hw2⟩ :=
      two_word_arg_lookup_ret_r29 (by decide) lookup_mul64x64 hl_orig
    injection heq with hhd htl
    injection hhd with h1; injection h1 with h1'; subst h1'
    injection htl with hhd2 _
    injection hhd2 with h2; injection h2 with h2'; subst h2'
    exact ⟨hw1, hw2⟩
  · intro t values body callee retShape v cpost _ _ ⟨hnt_lk, hs, hn, cw, ebw, hx, heb⟩ _ _ _ hlf ⟨lo, hi, hv, hexact⟩
    subst hv
    let res := setVarHOLFinite (ofString "dc") (.rStruct [.val (.word lo), .val (.word hi)])
      { cpost with locals := t.locals }
    have hm_cp : cpost.memory = t.memory := show cpost.memory = (callEntryStateHOLFinite t callee).memory by rw [hlf]
    have hg_cp : cpost.globals = t.globals := show cpost.globals = (callEntryStateHOLFinite t callee).globals by rw [hlf]
    have hm32_res : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
      have hg_ev : globN res "ev" = globN t "ev" := globN_congr hg_cp ▸ rfl
      rw [hg_ev]; dsimp only [res, setVarHOLFinite]; unfold memW; rw [hm_cp]
    refine ⟨?_, ?_, ?_, cw, ebw, lo, hi, ?_, ?_, ?_, hexact⟩
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "dc" ≠ ofString "ntopics")] using hnt_lk
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "dc" ≠ ofString "start")] using hs
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "dc" ≠ ofString "n")] using hn
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "dc" ≠ ofString "x")] using hx
    · rw [hm32_res]; exact heb
    · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Unpack cw, ebw, lo, hi before Step 7
  intro t6 hc6 hi6 hhm6 hwf6 hlen6 hR6 ⟨hnt_lk6, hs6, hn6, cw, ebw, lo, hi, hx6, heb6, hdc6, hexact6⟩ hnt6
  have hpos_base : 0 < (375#64 + 375#64 * nt).toNat := by
    have hm : (375#64 * nt).toNat = 375 * nt.toNat := by
      rw [BitVec.toNat_mul]
      change (375 * nt.toNat) % 2 ^ 64 = _
      rw [Nat.mod_eq_of_lt (by omega)]
    rw [BitVec.toNat_add, hm]
    change 0 < (375 + 375 * nt.toNat) % 2 ^ 64
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  suffices hstep7 : HandlerRunBoth W s0
      (fun t =>
        t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
        t.locals.lookup (ofString "start") = some startVal ∧
        t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨ (ebw.toNat % 32 = 0 ∧ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37)) ∧
        t.locals.lookup (ofString "dc") = some (.rStruct [.val (.word lo), .val (.word hi)])) false
      (.decCall (ofString "cost") .one (ofString "add_sat")
        [.op .add [.const 375#64, .panop .mul [.const 375#64, .var .local (ofString "ntopics")]],
         .rfield 0 (.var .local (ofString "x"))]
        (.seq
          (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "dc"))) (.const 0#64))
            (.assign .local (ofString "cost") (.const 18446744073709551615#64))
            (.call (some (some (.local, ofString "cost"), none)) (ofString "add_sat")
              [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))]))
          (.seq
            (.call (some (none, none)) (ofString "charge_gas") [.var .local (ofString "cost")])
            opLogPostChargeProg))) by
    exact hstep7 t6 hc6 hi6 hhm6 hwf6 hlen6 hR6 ⟨hnt_lk6, hs6, hn6, hx6, heb6, hdc6⟩ hnt6
  -- Step 7: cost := add_sat(375 + 375 * ntopics, x.0)
  apply HandlerRunBoth.decCall_ro (Q := fun t =>
    t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
    t.locals.lookup (ofString "start") = some startVal ∧
    t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
    t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
    (ebw = 0#64 ∨ (ebw.toNat % 32 = 0 ∧ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37)) ∧
    t.locals.lookup (ofString "dc") = some (.rStruct [.val (.word lo), .val (.word hi)]) ∧
    ∃ base : BitVec 64,
      t.locals.lookup (ofString "cost") = some (.val (.word base)) ∧ 0 < base.toNat)
    (by decide) eps_add_sat_pos
  · intro t values body' callee ret' hc _ _ ⟨hnt_lk, _, _, hx, _, _⟩ hargs hl
    have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
        [.op .add [.const 375#64, .panop .mul [.const 375#64, .var .local (ofString "ntopics")]],
         .rfield 0 (.var .local (ofString "x"))] =
        some [.val (.word (375#64 + 375#64 * nt)), .val (.word cw)] := by
      rw [evalListHOLFinite_eq_toExact]
      simp [evalListHOLExact, evalHOLExact, hnt_lk, hx, valueIsWord, valueWord, panOpHOL, wordOpHOL, wordOp]
    rw [hev] at hargs; injection hargs with hvs; subst hvs
    have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat")
        [.val (.word (375#64 + 375#64 * nt)), .val (.word cw)] = some (body', callee, ret') := by rwa [← hc]
    obtain ⟨_, _, a, _, heq, ha, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
    injection heq with hhd _
    injection hhd with h1; injection h1 with h2; subst h2
    exact ⟨_, ha, hpos_base⟩
  · intro t values body callee retShape v cpost _ _ ⟨hnt_lk, hs, hn, hx, heb, hdc⟩ _ _ _ hlf ⟨base, hv, hpos⟩
    subst hv
    let res := setVarHOLFinite (ofString "cost") (.val (.word base)) { cpost with locals := t.locals }
    have hm_cp : cpost.memory = t.memory := show cpost.memory = (callEntryStateHOLFinite t callee).memory by rw [hlf]
    have hg_cp : cpost.globals = t.globals := show cpost.globals = (callEntryStateHOLFinite t callee).globals by rw [hlf]
    have hm32_res : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
      have hg_ev : globN res "ev" = globN t "ev" := globN_congr hg_cp ▸ rfl
      rw [hg_ev]; dsimp only [res, setVarHOLFinite]; unfold memW; rw [hm_cp]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, base, ?_, hpos⟩
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "cost" ≠ ofString "ntopics")] using hnt_lk
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "cost" ≠ ofString "start")] using hs
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "cost" ≠ ofString "n")] using hn
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "cost" ≠ ofString "x")] using hx
    · rw [hm32_res]; exact heb
    · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
        (by decide : ofString "cost" ≠ ofString "dc")] using hdc
    · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  -- Step 8: if dc.1 != 0 then cost := 2^64 - 1 else cost := add_sat(cost, dc.0)
  apply HandlerRunBoth.seq_ite_unit
  · -- Branch 8a: dc.1 != 0 -> saturated cost -> charge_gas never returns
    intro t w _ _ _
    apply HandlerRunBoth.seq_assign_local (Q := fun s =>
      s.locals.lookup (ofString "cost") = some (.val (.word 18446744073709551615#64)))
    · intro s v he _
      have hv : v = .val (.word 18446744073709551615#64) := by simpa [evalHOLExact] using he.symm
      subst hv
      simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    · apply HandlerRunBoth.seq_charge_gas_exact (Q := fun _ => False)
      · intro s w' he hP
        have hw' : w' = 18446744073709551615#64 := by simpa [evalHOLExact, hP] using he.symm
        subst hw'; decide
      · intro s _ amtw he hlt _ _ hP _ _ _ _
        have hw' : amtw = 18446744073709551615#64 := by simpa [evalHOLExact, hP] using he.symm
        subst hw'; norm_num at hlt
      · intro _ _ _ _ _ _ _ hFalse _
        exact False.elim hFalse
  · -- Branch 8b: dc.1 == 0 -> hi = 0 -> nw.toNat < 2 ^ 61
    intro t8 ⟨_, _, _, _, _, hdc_t8, _⟩ hcond0
    have hhi0 : hi = 0#64 := by
      simp only [evalHOLExact, evalListHOLExact, hdc_t8, valueIsWord, valueWord,
        Compiler.Encoders.Asm.wordCmpHOL] at hcond0
      by_cases hne : hi ≠ 0#64
      · simp [hne] at hcond0
      · exact Classical.not_not.mp hne
    have hn_lt : nw.toNat < 2 ^ 61 := by
      have ⟨_, h8lt⟩ := hexact6 hhi0
      omega
    -- Step 8b call: cost := add_sat(cost, dc.0)
    apply HandlerRunBoth.seq_call_assign_local_ro (Q := fun t =>
      t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
      t.locals.lookup (ofString "start") = some startVal ∧
      t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
      t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
      (ebw = 0#64 ∨ (ebw.toNat % 32 = 0 ∧ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37)) ∧
      ∃ costw : BitVec 64,
        t.locals.lookup (ofString "cost") = some (.val (.word costw)) ∧ 0 < costw.toNat)
      (by decide) eps_add_sat_pos
    · intro t values body' callee ret' hc _ _ ⟨_, _, _, _, _, hdc, base, hcost, hpos_b⟩ hargs hl
      have hev : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.var .local (ofString "cost"), .rfield 0 (.var .local (ofString "dc"))] =
          some [.val (.word base), .val (.word lo)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hcost, hdc]
      rw [hev] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat")
          [.val (.word base), .val (.word lo)] = some (body', callee, ret') := by rwa [← hc]
      obtain ⟨_, _, a, _, heq, ha, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      injection heq with hhd _
      injection hhd with h1; injection h1 with h2; subst h2
      exact ⟨_, ha, hpos_b⟩
    · intro t values body callee retShape v cpost _ _ ⟨hnt_lk, hs, hn, hx, heb, _, _⟩ _ _ hlf ⟨costw, hv, hpos_c⟩
      subst hv
      let res := setVarHOLFinite (ofString "cost") (.val (.word costw)) { cpost with locals := t.locals }
      have hm_cp : cpost.memory = t.memory := show cpost.memory = (callEntryStateHOLFinite t callee).memory by rw [hlf]
      have hg_cp : cpost.globals = t.globals := show cpost.globals = (callEntryStateHOLFinite t callee).globals by rw [hlf]
      have hm32_res : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg_ev : globN res "ev" = globN t "ev" := globN_congr hg_cp ▸ rfl
        rw [hg_ev]; dsimp only [res, setVarHOLFinite]; unfold memW; rw [hm_cp]
      refine ⟨?_, ?_, ?_, ?_, ?_, costw, ?_, hpos_c⟩
      · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          (by decide : ofString "cost" ≠ ofString "ntopics")] using hnt_lk
      · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          (by decide : ofString "cost" ≠ ofString "start")] using hs
      · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          (by decide : ofString "cost" ≠ ofString "n")] using hn
      · simpa [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          (by decide : ofString "cost" ≠ ofString "x")] using hx
      · rw [hm32_res]; exact heb
      · simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    -- Step 9: charge_gas(cost) followed by opLogPostChargeProg
    · apply HandlerRunBoth.seq_charge_gas_exact (Q := fun t =>
        t.locals.lookup (ofString "ntopics") = some (.val (.word nt)) ∧
        t.locals.lookup (ofString "start") = some startVal ∧
        t.locals.lookup (ofString "n") = some (.val (.word nw)) ∧
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨ (ebw.toNat % 32 = 0 ∧ memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37)))
      · intro t w he ⟨_, _, _, _, _, costw, hcost, hpos_c⟩
        have hw : w = costw := by simpa [evalHOLExact, hcost] using he.symm
        subst hw; exact hpos_c
      · intro t cpost amtw _ _ _ _ ⟨hnt_lk, hs, hn, hx, heb, _⟩ _ hglob_cp _ hmem_cp
        let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
        have hm32_res : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
          have hg_ev : globN res "ev" = globN t "ev" := globN_congr hglob_cp ▸ rfl
          rw [hg_ev]; exact hmem_cp 32 (by simp)
        refine ⟨hnt_lk, hs, hn, hx, ?_⟩
        rw [hm32_res]; exact heb
      · intro t9 hc9 hi9 hhm9 hwf9 hlen9 hR9 ⟨hnt_lk9, hs9, hn9, hx9, heb9⟩ hnt9
        simp only [↓reduceIte] at hR9
        obtain ⟨S, Nd, hInvW9⟩ := evmInvWith_of_evmInv hi9
        exact op_log_post_charge_both_g09 hc9 hInvW9 hhm9 hwf9 hlen9 hR9
          hnt4 hn_lt hnt_lk9 hn9 hs9 hx9 heb9 hnt9

private theorem chainLinks_g09_iff_bridge_r29 (m : Nat → Nat) :
    ∀ xs : List Ivl, Group09ChainWF.ChainLinks m xs ↔ HeadMemBridge.ChainLinks m xs
  | [] => Iff.rfl
  | [_] => Iff.rfl
  | _ :: b :: rest =>
    and_congr_right fun _ => chainLinks_g09_iff_bridge_r29 m (b :: rest)

private theorem headMemChainWF_g09_iff_bridge_r29 {F : Type}
    (s : PanSemStateFiniteExact 64 F) :
    Group09ChainWF.HeadMemChainWF s ↔ HeadMemBridge.HeadMemChainWF s :=
  and_congr_right fun _ =>
    and_congr_right fun _ => chainLinks_g09_iff_bridge_r29 (memW s) (evmChain s)

/-- Discharges `OpLogBoundedAlignedSpec` (`ntopics ≤ 4`, `EvmRun ∧ HeadMemAligned`) with 0 `sorry`. -/
theorem op_log_bounded_aligned_spec : OpLogBoundedAlignedSpec := by
  refine ⟨_, _, _, lookup_op_log, ?_⟩
  intro F s hc ⟨⟨⟨hInv, _⟩, hHM⟩, nt, hnt_lk, hnt4⟩ _ hnt_prog
  exact (op_log_body_both_r29 (W := False) s hc hInv hHM False.elim hnt_lk hnt4 hnt_prog).1

/-- Discharges `OpLogBoundedChainSpec` (`ntopics ≤ 4`, `EvmInv ∧ HeadMemBridge.HeadMemChainWF ∧ ¬ EvmDone`)
with 0 `sorry`. -/
theorem op_log_bounded_chain_spec : OpLogBoundedChainSpec := by
  refine ⟨_, _, _, lookup_op_log, ?_⟩
  intro F s hc ⟨⟨hInv, hWF_br, _⟩, nt, hnt_lk, hnt4⟩ _ hnt_prog
  have hWF_g09 : Group09ChainWF.HeadMemChainWF s :=
    (headMemChainWF_g09_iff_bridge_r29 s).mpr hWF_br
  have hHM : HeadMemAligned s := Group09ChainWF.headMemChainWF_headMemAligned hWF_g09
  have hstep := (op_log_body_both_r29 (W := True) s hc hInv hHM (fun _ => hWF_g09) hnt_lk hnt4 hnt_prog).2 trivial
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨⟨hinv', hwf'⟩, hpot⟩ := hstep.1 hret
    exact ⟨⟨hinv', (headMemChainWF_g09_iff_bridge_r29 _).mp hwf'⟩, hpot⟩
  · obtain ⟨⟨hinv', hwf'⟩, hlen, hr⟩ := hstep.2 herr
    exact ⟨⟨hinv', (headMemChainWF_g09_iff_bridge_r29 _).mp hwf'⟩, hlen, hr⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
