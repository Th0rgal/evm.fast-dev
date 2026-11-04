import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush

/-! # OpHandlerSpec Group 06a: control-flow opcodes (`op_stop`, `op_jump`, `op_jumpi`, `op_pc`, `op_gas`, `op_jumpdest`) -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
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
open InitECandidate.Solver.Wave8Contracts.M23

/-! ## 1. Reusable `HandlerRun` combinators for `nonStructFrameOffs` stores, `EvmDone`, and 4-word locals -/

private theorem store_some_eq_error_b {F : Type} {s post : PanSemStateFiniteExact 64 F}
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

theorem ev_word_bounds {F : Type} {t : PanSemStateFiniteExact 64 F} (hInv : EvmInv t) :
    globN t "ev" + 280 ≤ 2 ^ 64 ∧
    ∃ evw : BitVec 64,
      t.globals.lookup (ofString "ev") = some (.val (.word evw)) ∧
      evw.toNat = globN t "ev" := by
  have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN t "ev" := by
    have hin := (hFW0.1 (globN t "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  exact ⟨hb_ev, global_word_of_pos t "ev" hev_pos⟩

theorem shapeEq_comb4_iff (v : ValueHOL 64) :
    shapeEqHOL (shapeOfHOLExact v) (.comb [.one, .one, .one, .one]) = true →
    ∃ w0 w1 w2 w3 : BitVec 64,
      v = .rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)] := by
  rcases v with _ | fs | _
  · simp [shapeOfHOLExact, shapeEqHOL]
  · rcases fs with _ | ⟨f0, _ | ⟨f1, _ | ⟨f2, _ | ⟨f3, _ | _⟩⟩⟩⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
    · simp only [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL, List.map, Bool.and_eq_true, Bool.and_true]
      rintro ⟨h0, h1, h2, h3⟩
      rcases f0 with ⟨⟨w0⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h0
      rcases f1 with ⟨⟨w1⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h1
      rcases f2 with ⟨⟨w2⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h2
      rcases f3 with ⟨⟨w3⟩⟩ | _ | _ <;> try simp [shapeOfHOLExact, shapeEqHOL] at h3
      exact ⟨w0, w1, w2, w3, rfl⟩
    · simp [shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  · simp [shapeOfHOLExact, shapeEqHOL]

def IsStruct4Local {F : Type} (nm : MlS) (t : PanSemStateFiniteExact 64 F) : Prop :=
  ∃ w0 w1 w2 w3 : BitVec 64,
    t.locals.lookup nm = some (.rStruct [.val (.word w0), .val (.word w1), .val (.word w2), .val (.word w3)])

private theorem rbound_step_b {charged : Bool} {r1 r2 r0 : Nat}
    (h1 : r2 ≤ r1) (h2 : if charged then r1 < r0 else r1 ≤ r0) :
    if charged then r2 < r0 else r2 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h2 ⊢ <;> omega

private theorem rbound_to_le_b {charged : Bool} {r1 r0 : Nat}
    (h : if charged then r1 < r0 else r1 ≤ r0) : r1 ≤ r0 := by
  cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at h <;> omega

/-- Shape-aware `HandlerRun.decCall`: carries `shapeEqHOL (shapeOfHOLExact v) sh = true` into `hstep`. -/
theorem HandlerRun.decCall_shaped {F : Type} {s0 : PanSemStateFiniteExact 64 F}
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
      shapeEqHOL (shapeOfHOLExact v) sh = true →
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
              have hsh_v : shapeEqHOL (shapeOfHOLExact v) sh = true := by
                simp only [Bool.and_eq_true] at hsh_ok; exact hsh_ok.1
              obtain ⟨hInv_cp, hch_cp, hR_cp, hQc_cp⟩ := (hQ (by simp)).1 v rfl
              let resumed := setVarHOLFinite nm v { cpost with locals := t.locals }
              have hcode_res : resumed.code = originalRuntimeCode := hmeta.trans hc
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost resumed.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 :=
                rbound_step_b (by rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; exact hR_cp) hR
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hsh_v hargs hl_orig hInv_cp hch_cp hQc_cp
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
              · have := rbound_to_le_b hR; rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi _ =>
            refine opDispatchPost_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

theorem HandlerRun.decCall_stack_pop_s4 {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {nm : MlS} {cont : ProgHOL 64}
    (hP_loc : ∀ t (cpost : PanSemStateFiniteExact 64 F) (v : ValueHOL 64), P t →
      P (setVarHOLFinite nm v { cpost with locals := t.locals }))
    (hcont : HandlerRun s0 (fun t => P t ∧ IsStruct4Local nm t) charged cont) :
    HandlerRun s0 P charged (.decCall nm (.comb [.one, .one, .one, .one]) (ofString "stack_pop") [] cont) := by
  refine HandlerRun.decCall_shaped eps_stack_pop
    (fun _ _ _ _ _ _ _ _ _ _ => trivial) ?_ hcont
  intro t _ _ _ _ v cpost _ hP hsh _ _ _ _ _
  obtain ⟨w0, w1, w2, w3, rfl⟩ := shapeEq_comb4_iff v hsh
  refine ⟨hP_loc t cpost _ hP, w0, w1, w2, w3, ?_⟩
  simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]

theorem eval_rField_of_struct4 {F : Type} {t : PanSemStateFiniteExact 64 F} {nm : MlS}
    (hs4 : IsStruct4Local nm t) (idx : Nat) (hidx : idx < 4) :
    ∀ v : ValueHOL 64,
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.rfield idx (.var .local nm)) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := by
  obtain ⟨w0, w1, w2, w3, hlk⟩ := hs4
  intro v hv
  simp only [evalHOLExact, hlk] at hv
  rcases idx with _ | _ | _ | _ | _
  · simp at hv; exact ⟨w0, hv.symm⟩
  · simp at hv; exact ⟨w1, hv.symm⟩
  · simp at hv; exact ⟨w2, hv.symm⟩
  · simp at hv; exact ⟨w3, hv.symm⟩
  · omega

theorem HandlerRun.seq_store_ev_nonstruct {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    (off : Nat) (hoff : off ∈ nonStructFrameOffs) {valExp : ExpHOL 64} {cont : ProgHOL 64}
    (hval : ∀ (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
      P t →
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hstep : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) valExp =
        some (.val (.word w)) →
      EvmInv t → P t →
      Q { t with memory := updW t.memory (BitVec.ofNat 64 (globN t "ev" + off)) w })
    (hcont : HandlerRun s0 Q charged cont) :
    HandlerRun s0 P charged
      (.seq (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) cont) := by
  intro t hc hInv hlen hR hP hnt
  have hoff_lt : off + 8 ≤ 280 := by
    simp only [nonStructFrameOffs, List.mem_cons, List.not_mem_nil, or_false] at hoff
    rcases hoff with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hst : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 off)]) valExp) with ⟨r1, t1⟩
  simp only [hst] at hnt ⊢
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_error_b hst; subst herr
    exact opDispatchPost_error s0 t1
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨w, hw_ev, ht1_eq⟩ := store_global_off_word (t := t) (post := t1)
      (gname := "ev") (gbase := globN t "ev") (off := off) hevw hevw_nat (by omega)
      (fun v hv => hval t v hP hv) hst
    have hGt1 : GuestInv t1 := guestInv_congr (s := t)
      (by simp [ht1_eq]) (by simp [ht1_eq]) (by simp [ht1_eq]) (by simp [ht1_eq]) hInv.1.1
    have hmem_out : ∀ x : BitVec 64,
        (∀ off' ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN t "ev" + off')) →
        t1.memory x = t.memory x := by
      intro x hx
      rw [ht1_eq]; dsimp only [updW]
      rw [if_neg (hx off hoff)]
    obtain ⟨hInv1, hch1, hR1_eq⟩ := evmInv_of_head_nonstruct hInv hGt1
      (by simp [ht1_eq]) (by simp [ht1_eq]) hmem_out
    have hQ1 : Q t1 := by rw [ht1_eq]; exact hstep t w hw_ev hInv hP
    exact hcont t1 (by rw [ht1_eq]; exact hc) hInv1 (by rw [hch1]; exact hlen) (by rw [hR1_eq]; exact hR) hQ1 hnt

theorem HandlerRun.ret_done {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    (hRun : EvmRun s0) {P : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    (hdone : ∀ t, EvmInv t → P t → EvmDone t) (e : ExpHOL 64) :
    HandlerRun s0 P charged (.return e) := by
  intro t _ hInv hlen hR hP _
  have hR_le : evmR t ≤ evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  rw [evaluateHOLFiniteState_return]
  split
  · exact opDispatchPost_error s0 t
  · split
    · have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      have hDone' : EvmDone (emptyLocalsHOLFinite t) := by
        unfold EvmDone globN memW
        exact hdone t hInv hP
      refine ⟨fun _ => ⟨hInv', evmPot_lt_of_done hRun hInv' hDone'
        (by rw [hc.2.2.1, hlen]) (by rw [hc.2.1]; exact hR_le)⟩, ?_⟩
      rintro ⟨_, h⟩; cases h
    · exact opDispatchPost_error s0 t

/-! ## 2. `eps_is_valid_jumpdest` and `eps_pc_add_keep104` -/

theorem eps_is_valid_jumpdest :
    EvmPreservingSpec (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "is_valid_jumpdest") :=
  eps_of_readOnly 464 (by rw [guestAst_len]; decide) Guest.Software.guestFn_is_valid_jumpdest rfl
    opRoCallees opRoCallees_good rfl

/-- Refined `pc_add` spec showing `memW post (ev + 104) = memW s (ev + 104)` (used by `op_stop`, `op_return`). -/
theorem eps_pc_add_keep104 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => post.globals = s.globals ∧ memW post (globN s "ev" + 104) = memW s (globN s "ev" + 104))
      (ofString "pc_add") := by
  refine ⟨_, _, _, lookup_pc_add, ?_⟩
  intro F s _ hInv _ _ _
  have hbody : sourceFnBody Guest.Software.guestFn_pc_add =
      .seq
        (.store (.op .add [.var .global (ofString "ev"), .const 0])
          (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")]))
        (.return (.const 0)) := rfl
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  dsimp only; rw [hbody, evaluateHOLFiniteState_seq_line780]
  rcases hst : evaluateHOLFiniteState s
      (.store (.op .add [.var .global (ofString "ev"), .const 0])
        (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")])) with ⟨r1, s1⟩
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_error_b hst; subst herr
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
      rw [if_neg (hx 0 (by simp [nonStructFrameOffs]))]
    obtain ⟨hInv_p, hch_p, hR_p⟩ := evmInv_of_head_nonstruct hInv hGp hglob_p hbe_p hmem_out
    have hm104 : memW post (globN s "ev" + 104) = memW s (globN s "ev" + 104) := by
      change memW s1 (globN s "ev" + 104) = memW s (globN s "ev" + 104)
      rw [hs1_eq]
      exact memW_updW_ne s (globN s "ev" + 0) (globN s "ev" + 104) w1 (by omega) (by omega) (by omega)
    exact ⟨fun _ _ => ⟨hInv_p, hch_p, le_of_eq hR_p, hglob_p, hm104⟩, by rintro ⟨_, h⟩; cases h⟩

/-! ## 3. Group 06a opcode handler proofs (`op_stop`, `op_jump`, `op_jumpi`, `op_pc`, `op_gas`, `op_jumpdest`) -/

theorem op_stop_spec : OpHandlerSpec (ofString "op_stop") := by
  refine opHandlerSpec_of_run 502 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_stop rfl ?_
  intro F s0 hRun
  dsimp only [Guest.Software.guestFn_op_stop, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine HandlerRun.seq_store_ev_nonstruct (Q := fun t => memW t (globN t "ev" + 104) = 0)
    104 (by simp [nonStructFrameOffs])
    (fun _ v _ hv => by
      change some (ValueHOL.val (.word 0#64)) = some v at hv
      injection hv with hv'
      exact ⟨0, hv'.symm⟩)
    (fun t w hw _ _ => by
      change some (ValueHOL.val (.word 0#64)) = some (.val (.word w)) at hw
      injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3; subst hw3
      simpa [globN] using memW_updW_same t (globN t "ev" + 104) 0)
    ?_
  refine HandlerRun.seq_call (Q := fun t => memW t (globN t "ev" + 104) = 0)
    eps_pc_add_keep104
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ _ cpost _ hP _ _ _ _ ⟨hg_cp, hm104⟩ => by
      have hg_ce : globN (t.callEntryStateHOLFinite callee) "ev" = globN t "ev" := rfl
      have hg_eq : globN cpost "ev" = globN t "ev" := by
        rw [globN_congr hg_cp]; rfl
      change memW cpost (globN cpost "ev" + 104) = 0
      rw [hg_eq]
      rw [hg_ce] at hm104
      exact hm104.trans hP)
    (HandlerRun.ret_done hRun (fun _ _ hP => Or.inr (Or.inl hP)) _)

theorem op_jump_spec : OpHandlerSpec (ofString "op_jump") := by
  refine opHandlerSpec_of_run 503 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_jump rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_jump, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine HandlerRun.decCall_stack_pop_s4 (fun _ _ _ _ => trivial) ?_
  refine HandlerRun.seq_charge_gas (Q := fun t => IsStruct4Local (ofString "dest") t)
    (fun _ w hw _ _ => by
      change some (ValueHOL.val (.word 8#64)) = some (.val (.word w)) at hw
      injection hw with h1; injection h1 with h2; injection h2 with h3; subst h3; decide)
    (fun _ _ _ ⟨_, hs4⟩ _ _ _ => hs4) ?_
  refine HandlerRun.decCall (Q := fun t => IsStruct4Local (ofString "dest") t)
    eps_is_valid_jumpdest
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ _ _ v cpost _ hs4 _ _ _ _ _ => by
      obtain ⟨w0, w1, w2, w3, hlk⟩ := hs4
      refine ⟨w0, w1, w2, w3, ?_⟩
      have hne : ofString "ok" ≠ ofString "dest" := by decide
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hlk) ?_
  refine HandlerRun.seq_ite_raise_skip (fun _ _ _ h => h) ?_
  exact HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True)
    0 (by simp [nonStructFrameOffs])
    (fun _ v hs4 hv => eval_rField_of_struct4 hs4 0 (by omega) v hv)
    (fun _ _ _ _ _ => trivial)
    (HandlerRun.ret _)

theorem op_jumpi_spec : OpHandlerSpec (ofString "op_jumpi") := by
  refine opHandlerSpec_of_run 504 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_jumpi rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_jumpi, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  refine HandlerRun.decCall_stack_pop_s4 (fun _ _ _ _ => trivial) ?_
  refine HandlerRun.decCall (Q := fun t => IsStruct4Local (ofString "dest") t)
    eps_stack_pop
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ ⟨_, hs4⟩ _ _ _ _ _ => by
      obtain ⟨w0, w1, w2, w3, hlk⟩ := hs4
      refine ⟨w0, w1, w2, w3, ?_⟩
      have hne : ofString "cond" ≠ ofString "dest" := by decide
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hlk) ?_
  refine HandlerRun.seq_charge_gas (Q := fun t => IsStruct4Local (ofString "dest") t)
    (fun _ w hw _ _ => by
      change some (ValueHOL.val (.word 10#64)) = some (.val (.word w)) at hw
      injection hw with h1; injection h1 with h2; injection h2 with h3; subst h3; decide)
    (fun _ _ _ hs4 _ _ _ => hs4) ?_
  refine HandlerRun.decCall (Q := fun t => IsStruct4Local (ofString "dest") t)
    eps_u256_is_zero
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ _ _ _ hs4 _ _ _ _ _ => by
      obtain ⟨w0, w1, w2, w3, hlk⟩ := hs4
      refine ⟨w0, w1, w2, w3, ?_⟩
      have hne : ofString "z" ≠ ofString "dest" := by decide
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hlk) ?_
  -- Next is `Prog.seq (Prog.ite (z != 0) (pc_add(1); return 0) skip) (decCall ok := is_valid_jumpdest ...)`
  -- Note: when the `yes` branch ends with `return 0`, it NEVER falls through `.seq`, whereas `no` is `skip`!
  intro t hc hInv hlen hR hs4 hnt
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hnt ⊢
  revert hnt
  split
  · rename_i cw hcw
    by_cases hcw0 : cw = 0
    · subst hcw0
      simp only [↓reduceIte, evaluateHOLFiniteState_skip]
      intro hnt
      refine (HandlerRun.decCall (Q := fun u => IsStruct4Local (ofString "dest") u)
        eps_is_valid_jumpdest
        (fun _ _ _ _ _ _ _ _ _ _ => trivial)
        (fun _ _ _ _ _ _ _ _ hs4' _ _ _ _ _ => by
          obtain ⟨w0, w1, w2, w3, hlk⟩ := hs4'
          refine ⟨w0, w1, w2, w3, ?_⟩
          have hne : ofString "ok" ≠ ofString "dest" := by decide
          simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne] using hlk)
        (HandlerRun.seq_ite_raise_skip (fun _ _ _ h => h)
          (HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True)
            0 (by simp [nonStructFrameOffs])
            (fun _ v hs4' hv => eval_rField_of_struct4 hs4' 0 (by omega) v hv)
            (fun _ _ _ _ _ => trivial)
            (HandlerRun.ret _)))) t hc hInv hlen hR hs4 hnt
    · simp only [hcw0, ↓reduceIte]
      -- In `yes` branch: `pc_add(1); return 0`. Since `return 0` never returns `none`, `.seq` terminates immediately!
      have hyes_run : HandlerRun s0 (fun _ => True) true
          (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64))) :=
        HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)
      rcases hyes_ev : evaluateHOLFiniteState t
          (.seq (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) (.return (.const 0#64))) with ⟨ry, sy⟩
      cases ry with
      | none =>
        exfalso
        rw [evaluateHOLFiniteState_seq_line780] at hyes_ev
        rcases hcall : evaluateHOLFiniteState t (.call (some (none, none)) (ofString "pc_add") [.const 1#64]) with ⟨rc, sc⟩
        rw [hcall] at hyes_ev
        cases rc with
        | some _ => dsimp only at hyes_ev; injection hyes_ev with hr; cases hr
        | none =>
          dsimp only at hyes_ev
          rw [evaluateHOLFiniteState_return] at hyes_ev
          split at hyes_ev
          · injection hyes_ev with hr; cases hr
          · split at hyes_ev <;> (injection hyes_ev with hr; cases hr)
      | some r0 =>
        dsimp only [Option.map, List.map, InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural]
        rw [hyes_ev]; dsimp only
        intro hnt
        have hp := hyes_run t hc hInv hlen hR trivial (by rw [hyes_ev]; exact hnt)
        rw [hyes_ev] at hp; exact hp
  · intro _; exact opDispatchPost_error s0 t

theorem op_pc_spec : OpHandlerSpec (ofString "op_pc") := by
  refine opHandlerSpec_of_run 505 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_pc rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_pc, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_stack_push_word
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

theorem op_gas_spec : OpHandlerSpec (ofString "op_gas") := by
  refine opHandlerSpec_of_run 506 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_gas rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_gas, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_stack_push_word
        (HandlerRun.seq_call_simple eps_pc_add
          (HandlerRun.ret _)))

theorem op_jumpdest_spec : OpHandlerSpec (ofString "op_jumpdest") := by
  refine opHandlerSpec_of_run 507 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_jumpdest rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_jumpdest, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.seq_call_simple eps_pc_add
        (HandlerRun.ret _))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
