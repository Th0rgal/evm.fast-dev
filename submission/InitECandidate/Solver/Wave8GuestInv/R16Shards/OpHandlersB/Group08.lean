import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.ExtendMemoryHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers

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
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8Contracts.M23

theorem lookup_charge_with_memory :
    originalRuntimeCode.lookup (ofString "charge_with_memory") =
      some ([(ofString "base", .one),
             (ofString "start", .comb [.one, .one, .one, .one]),
             (ofString "size", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_charge_with_memory, .one) :=
  lookup_of_guestAst_getElem 461 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_charge_with_memory) rfl

theorem lookup_op_mload :
    originalRuntimeCode.lookup (ofString "op_mload") =
      some ([], sourceFnBody Guest.Software.guestFn_op_mload, .one) :=
  lookup_of_guestAst_getElem 510 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_mload) rfl

private theorem store_some_eq_error_g08 {F : Type} {s post : PanSemStateFiniteExact 64 F}
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

private theorem headMemAligned_congr_head_only {F : Type}
    {s t : PanSemStateFiniteExact 64 F}
    (hg : t.globals = s.globals)
    (hmem : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
      memW t (globN s "ev" + off) = memW s (globN s "ev" + off))
    (h : HeadMemAligned s) : HeadMemAligned t := by
  have hgev : globN t "ev" = globN s "ev" := globN_eq_of_lookup_eq (by rw [hg])
  have hgfp : globN t "frame_mem_ptr" = globN s "frame_mem_ptr" := globN_eq_of_lookup_eq (by rw [hg])
  refine ⟨?_, ?_⟩
  · rw [hgev, hmem 32 (by simp)]; exact h.1
  · rw [hgev, hgfp, hmem 24 (by simp), hmem 40 (by simp)]; exact h.2

private theorem eps_stack_pop_preserves_headMem :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post =>
        post.globals = s.globals ∧
        (HeadMemAligned s → HeadMemAligned post))
      (ofString "stack_pop") := by
  refine ⟨_, _, _, lookup_stack_pop_pub, ?_⟩
  intro F s hcode hInv _ hlookup hnt
  obtain ⟨params_sp, body_sp, ret_sp, hlk_sp, hspec_sp⟩ := eps_stack_pop
  have hlk_eq : some ([], sourceFnBody Guest.Software.guestFn_stack_pop, ShapeHOL.comb [.one, .one, .one, .one]) =
      some (params_sp, body_sp, ret_sp) := lookup_stack_pop_pub.symm.trans hlk_sp
  injection hlk_eq with hprod
  rcases Prod.mk.inj hprod with ⟨rfl, hprod2⟩
  rcases Prod.mk.inj hprod2 with ⟨hbody_sp, rfl⟩
  subst hbody_sp
  have hs := hspec_sp s hcode hInv trivial hlookup hnt
  dsimp only at hs ⊢
  refine ⟨fun v hv => ?_, hs.2⟩
  obtain ⟨hInv_p, hch_p, hR_p, hglob_p⟩ := hs.1 v hv
  refine ⟨hInv_p, hch_p, hR_p, hglob_p, ?_⟩
  intro hHM
  have hhead_mem : (globN s "ev", globN s "cur_cont") ∈ evmChain s := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN s "ev" := by
    obtain ⟨hin, _⟩ := (hFW0.1 (globN s "ev", 280) (by simp)).1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos s "ev" hev_pos
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
  have hmem_ne16 : ∀ x : BitVec 64, x ≠ BitVec.ofNat 64 (globN s "ev" + 16) →
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_stack_pop)).2.memory x = s.memory x := by
    revert hv
    rw [hb, evaluateHOLFiniteState_dec_total]; dsimp only
    split
    · simp
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
            · simp
            · rename_i sp1 hsp1
              have hsp1_w : ∃ w : BitVec 64, sp1 = .val (.word w) := by
                simp only [evalHOLExact, wordOpHOL] at hsp1; revert hsp1
                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                · simp
                · dsimp only; split
                  · simp only [Option.map]
                    rcases wordOp .sub (vs.map valueWord) with _ | w
                    · simp
                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
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
                  have herr := store_some_eq_error_g08 hst; subst herr; simp
                | none =>
                  dsimp only
                  obtain ⟨w2, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                    (gname := "ev") (gbase := globN s "ev") (off := 16) hevw hevw_nat (by omega)
                    (fun u hu => by
                      have hsp2 : s2.locals.lookup (ofString "sp") = some (.val (.word spw)) := by
                        simp [s2, setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
                      change s2.locals.lookup (ofString "sp") = some u at hu
                      rw [hsp2] at hu; injection hu with hu'; exact ⟨spw, hu'.symm⟩) hst
                  intro _ x hx
                  rw [evaluateHOLFiniteState_return]
                  split
                  · dsimp only; rw [hs3_eq]; dsimp only [updW]; rw [if_neg hx]; rfl
                  · split
                    · dsimp only [emptyLocalsHOLFinite]; rw [hs3_eq]; dsimp only [updW]; rw [if_neg hx]; rfl
                    · dsimp only; rw [hs3_eq]; dsimp only [updW]; rw [if_neg hx]; rfl
              · simp
          · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 2)) with ⟨rr, sr⟩
            have hr_nn : rr ≠ none ∧ sr.globals = s.globals ∧ sr.memory = s.memory := by
              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
              split at hraise
              · split at hraise <;> (injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩)
              · injection hraise with h1 h2; subst h1 h2; exact ⟨by simp, rfl, rfl⟩
            cases rr with
            | none => exact absurd rfl hr_nn.1
            | some r0 =>
              dsimp only
              intro hres
              cases r0 <;> simp at hres
              rename_i vr
              subst hres
              intro x _
              change sr.memory x = s.memory x
              rw [hr_nn.2.2]
        · simp
      · simp
  refine headMemAligned_congr_head_only hglob_p (fun off hoff => ?_) hHM
  have hne_bv : BitVec.ofNat 64 (globN s "ev" + off) ≠ BitVec.ofNat 64 (globN s "ev" + 16) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    intro heq
    have htn := congrArg BitVec.toNat heq
    rcases hoff with rfl | rfl | rfl <;>
      (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
  unfold memW; rw [hmem_ne16 _ hne_bv]

private def CalleeBodyRun {F : Type} (s0 : PanSemStateFiniteExact 64 F)
    (P : PanSemStateFiniteExact 64 F → Prop) (charged : Bool)
    (prog : ProgHOL 64) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 F),
    t.code = originalRuntimeCode →
    EvmInv t →
    (evmChain t).length = (evmChain s0).length →
    (if charged then evmR t < evmR s0 else evmR t ≤ evmR s0) →
    P t →
    (evaluateHOLFiniteState t prog).1 ≠ some .timeOut →
    let out := evaluateHOLFiniteState t prog
    ((∃ v, out.1 = some (.returned v)) →
      EvmInv out.2 ∧ (evmChain out.2).length = (evmChain s0).length ∧ evmR out.2 < evmR s0) ∧
    (IsEvmErr out.1 →
      EvmInv out.2 ∧ (evmChain out.2).length = (evmChain s0).length ∧ evmR out.2 ≤ evmR s0) ∧
    (∀ r0, out.1 = some r0 →
      (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr out.1 →
      ∀ v', out.1 ≠ some (.returned v'))

private theorem calleeBodyRun_congr_lc {F : Type}
    {s0 post post' : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hp_lc : post' = { post with locals := post'.locals, clock := post'.clock })
    (h : ((∃ v, r = some (.returned v)) →
           EvmInv post ∧ (evmChain post).length = (evmChain s0).length ∧ evmR post < evmR s0) ∧
         (IsEvmErr r →
           EvmInv post ∧ (evmChain post).length = (evmChain s0).length ∧ evmR post ≤ evmR s0)) :
    ((∃ v, r = some (.returned v)) →
      EvmInv post' ∧ (evmChain post').length = (evmChain s0).length ∧ evmR post' < evmR s0) ∧
    (IsEvmErr r →
      EvmInv post' ∧ (evmChain post').length = (evmChain s0).length ∧ evmR post' ≤ evmR s0) := by
  have hp_m : post'.memory = post.memory := by rw [hp_lc]
  have hp_g : post'.globals = post.globals := by rw [hp_lc]
  have hp := evm_congr hp_m hp_g
  have hinv : EvmInv post → EvmInv post' := fun h0 => by
    rw [hp_lc]; exact localsFree_evmInv post post'.locals post'.clock h0
  refine ⟨fun hret => ?_, fun herr => ?_⟩
  · obtain ⟨hi, hlen, hlt⟩ := h.1 hret
    exact ⟨hinv hi, by rw [hp.2.2.1]; exact hlen, by rw [hp.2.1]; exact hlt⟩
  · obtain ⟨hi, hlen, hR⟩ := h.2 herr
    exact ⟨hinv hi, by rw [hp.2.2.1]; exact hlen, by rw [hp.2.1]; exact hR⟩

private theorem calleeBodyRun_error {F : Type} (s0 t : PanSemStateFiniteExact 64 F) :
    (((∃ v, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some (.returned v)) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t < evmR s0) ∧
     (IsEvmErr (some PanSemResultExact.error) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t ≤ evmR s0) ∧
     (∀ r0, (some PanSemResultExact.error : Option (PanSemResultExact 64)) = some r0 →
      (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr (some PanSemResultExact.error) →
      ∀ v', (some PanSemResultExact.error : Option (PanSemResultExact 64)) ≠ some (.returned v'))) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, h⟩; cases h
  · rintro ⟨_, h⟩; cases h
  · intro _ _ _ _ _ h; cases h

private theorem calleeBodyRun_other {F : Type} {s0 t : PanSemStateFiniteExact 64 F}
    {r : Option (PanSemResultExact 64)}
    (hnret : ∀ v, r ≠ some (.returned v)) (hnerr : ¬ IsEvmErr r) :
    (((∃ v, r = some (.returned v)) →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t < evmR s0) ∧
     (IsEvmErr r →
      EvmInv t ∧ (evmChain t).length = (evmChain s0).length ∧ evmR t ≤ evmR s0) ∧
     (∀ r0, r = some r0 → (∀ v, r0 ≠ .returned v) → ¬ IsEvmErr r → ∀ v', r ≠ some (.returned v'))) :=
  ⟨fun ⟨v, hv⟩ => (hnret v hv).elim, fun he => (hnerr he).elim, fun _ _ _ _ v' => hnret v'⟩

private theorem CalleeBodyRun.ret {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop} (e : ExpHOL 64) :
    CalleeBodyRun s0 P true (.return e) := by
  intro t _ hInv hlen hR _ _
  simp only [↓reduceIte] at hR
  dsimp only
  rw [evaluateHOLFiniteState_return]
  split
  · exact calleeBodyRun_error s0 t
  · split
    · have hInv' : EvmInv (emptyLocalsHOLFinite t) :=
        localsFree_evmInv t (emptyLocalsHOLFinite t).locals t.clock hInv
      have hc := evm_congr (s := t) (t := emptyLocalsHOLFinite t) rfl rfl
      refine ⟨fun _ => ⟨hInv', by rw [hc.2.2.1]; exact hlen, by rw [hc.2.1]; exact hR⟩, ?_, ?_⟩
      · rintro ⟨_, h⟩; cases h
      · intro r0 hr hnr _ _
        injection hr with hr'
        subst hr'
        exact (hnr _ rfl).elim
    · exact calleeBodyRun_error s0 t

private theorem CalleeBodyRun.decCall {F : Type} {s0 : PanSemStateFiniteExact 64 F}
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
    (hcont : CalleeBodyRun s0 Q charged cont) :
    CalleeBodyRun s0 P charged (.decCall nm sh fname args cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  dsimp only
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact calleeBodyRun_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRun_error s0 t
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
        | none => exact calleeBodyRun_error s0 cpost
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
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR ⊢ <;>
                  (rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega)
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              have hb := hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
              dsimp only at hb
              refine ⟨?_, ?_, fun r1 hr1 hnr1 hnerr1 v' => hb.2.2 r1 hr1 hnr1 hnerr1 v'⟩
              · exact (calleeBodyRun_congr_lc rfl ⟨hb.1, hb.2.1⟩).1
              · exact (calleeBodyRun_congr_lc rfl ⟨hb.1, hb.2.1⟩).2
            · exact calleeBodyRun_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hR_le : evmR t ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRun_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRun_error s0 cpost
          | «continue» => exact calleeBodyRun_error s0 cpost
          | finalFfi f =>
            refine calleeBodyRun_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRun_error s0 cpost.emptyLocalsHOLFinite

private theorem CalleeBodyRun.seq_call {F : Type} {s0 : PanSemStateFiniteExact 64 F}
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
    (hcont : CalleeBodyRun s0 Q charged cont) :
    CalleeBodyRun s0 P charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
  obtain ⟨params, body, retShape, hlook, hspec⟩ := hf
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args with _ | values
  · exact calleeBodyRun_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup fname values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRun_error s0 t
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
        | none => exact calleeBodyRun_error s0 cpost
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
              have hR_res : if charged then evmR resumed < evmR s0 else evmR resumed ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR ⊢ <;>
                  (rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega)
              have hQ_res : Q resumed := hstep t values body callee retShape v cpost hInv hP hargs hl_orig hInv_cp hch_cp hQc_cp
              exact hcont resumed hcode_res hInv_res hlen_res hR_res hQ_res (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact calleeBodyRun_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hch_cp, hR_cp⟩ := (hQ (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              have hR_le : evmR t ≤ evmR s0 := by
                cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRun_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRun_error s0 cpost
          | «continue» => exact calleeBodyRun_error s0 cpost
          | finalFfi f =>
            refine calleeBodyRun_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRun_error s0 cpost.emptyLocalsHOLFinite

private theorem CalleeBodyRun.seq_charge_gas_preserves_headMem {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P Q : PanSemStateFiniteExact 64 F → Prop} {charged : Bool}
    {amtExp : ExpHOL 64} {cont : ProgHOL 64}
    (hpos : ∀ t (w : BitVec 64),
      @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) amtExp =
        some (.val (.word w)) →
      EvmInv t → P t → 0 < w.toNat)
    (hstep : ∀ t cpost,
      EvmInv t → P t → EvmInv cpost → cpost.globals = t.globals →
      evmChain cpost = evmChain t →
      (∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
        memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off)) →
      Q { cpost with locals := t.locals })
    (hcont : CalleeBodyRun s0 Q true cont) :
    CalleeBodyRun s0 P charged (.seq (.call (some (none, none)) (ofString "charge_gas") [amtExp]) cont) := by
  intro t hc hInv hlen hR hP hnt
  have hR_le : evmR t ≤ evmR s0 := by
    cases charged <;> simp only [↓reduceIte, Bool.false_eq_true] at hR <;> omega
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
  rcases hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [amtExp] with _ | values
  · exact calleeBodyRun_error s0 t
  · simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite t.code.lookup (ofString "charge_gas") values with _ | ⟨body', callee, ret'⟩
    · exact calleeBodyRun_error s0 t
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
        let ce := callEntryStateHOLFinite t callee
        change cpost.code = t.code at hmeta
        cases res with
        | none => exact calleeBodyRun_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hglob_cp, hch_cp, hR_cp⟩ := hcg.1 v rfl
              have hmem_head_cp : ∀ off : Nat, off ∈ ([24, 32, 40] : List Nat) →
                  memW cpost (globN t "ev" + off) = memW t (globN t "ev" + off) := by
                intro off hoff
                have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
                have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
                have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
                dsimp only at hb_ev
                have hev_pos : 0 < globN t "ev" := by
                  obtain ⟨hin, _⟩ := (hFW0.1 (globN t "ev", 280) (by simp)).1
                  have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
                  rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
                obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
                have hevw_ce : ce.globals.lookup (ofString "ev") = some (.val (.word evw)) := hevw
                have hbody_cg : sourceFnBody Guest.Software.guestFn_charge_gas =
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
                have hmem_ne : ∀ x : BitVec 64,
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 64) →
                    x ≠ BitVec.ofNat 64 (globN t "ev" + 184) →
                    cpost.memory x = t.memory x := by
                  have hrun' := hrun
                  rw [hbody_cg, evaluateHOLFiniteState_dec_total] at hrun'; dsimp only at hrun'
                  split at hrun'
                  · simp at hrun'
                  · rename_i glv _
                    split at hrun'
                    · set s1 := setVarHOLFinite (ofString "gl") glv ce
                      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hrun'
                      split at hrun'
                      · split at hrun'
                        · simp only [evaluateHOLFiniteState_skip] at hrun'
                          rw [evaluateHOLFiniteState_seq_line780] at hrun'
                          rcases hst1 : evaluateHOLFiniteState s1
                              (.store (.op .add [.var .global (ofString "ev"), .const 64])
                                (.op .sub [.var .local (ofString "gl"), .var .local (ofString "amount")])) with ⟨r1, s2⟩
                          rw [hst1] at hrun'
                          cases r1 with
                          | some res1 =>
                            have herr1 := store_some_eq_error_g08 hst1; subst herr1; simp at hrun'
                          | none =>
                            dsimp only at hrun'
                            obtain ⟨w1, _, hs2_eq⟩ := store_global_off_word (t := s1) (post := s2)
                              (gname := "ev") (gbase := globN t "ev") (off := 64) hevw_ce hevw_nat (by omega)
                              (fun u hu => by
                                simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                rcases @evalListHOLExact 64 F _ s1.toExact (fun a => Classical.propDecidable (s1.memaddrs a)) _ with _ | vs
                                · simp
                                · dsimp only; split
                                  · simp only [Option.map]
                                    rcases wordOp .sub (vs.map valueWord) with _ | w
                                    · simp
                                    · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                  · simp) hst1
                            rw [evaluateHOLFiniteState_seq_line780] at hrun'
                            rcases hst2 : evaluateHOLFiniteState s2
                                (.store (.op .add [.var .global (ofString "ev"), .const 184])
                                  (.op .add
                                    [.load .one (.op .add [.var .global (ofString "ev"), .const 184]),
                                     .var .local (ofString "amount")])) with ⟨r2, s3⟩
                            rw [hst2] at hrun'
                            cases r2 with
                            | some res2 =>
                              have herr2 := store_some_eq_error_g08 hst2; subst herr2; simp at hrun'
                            | none =>
                              dsimp only at hrun'
                              obtain ⟨w2, _, hs3_eq⟩ := store_global_off_word (t := s2) (post := s3)
                                (gname := "ev") (gbase := globN t "ev") (off := 184)
                                (by rw [hs2_eq]; exact hevw_ce) hevw_nat (by omega)
                                (fun u hu => by
                                  simp only [evalHOLExact, wordOpHOL] at hu; revert hu
                                  rcases @evalListHOLExact 64 F _ s2.toExact (fun a => Classical.propDecidable (s2.memaddrs a)) _ with _ | vs
                                  · simp
                                  · dsimp only; split
                                    · simp only [Option.map]
                                      rcases wordOp .add (vs.map valueWord) with _ | w
                                      · simp
                                      · intro h'; injection h' with h''; exact ⟨w, h''.symm⟩
                                    · simp) hst2
                              rw [evaluateHOLFiniteState_return] at hrun'; dsimp only [evalHOLExact] at hrun'
                              have hsz0 : sizeOfShapeWithContextHOL s3.structs
                                  (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
                                simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
                              rw [if_pos hsz0] at hrun'; dsimp only at hrun'
                              injection hrun' with _ hcpost_eq
                              subst hcpost_eq
                              intro x hx64 hx184
                              dsimp only [emptyLocalsHOLFinite]
                              rw [hs3_eq]; dsimp only [updW]; rw [if_neg hx184]
                              rw [hs2_eq]; dsimp only [updW]; rw [if_neg hx64]
                              rfl
                        · rcases hraise : evaluateHOLFiniteState s1 (.raise (ofString "EvmErr") (.const 4)) with ⟨rr, sr⟩
                          rw [hraise] at hrun'
                          have hr_nn : rr ≠ none := by
                            rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                            split at hraise
                            · split at hraise <;> (injection hraise with h1 _; subst h1; simp)
                            · injection hraise with h1 _; subst h1; simp
                          cases rr with
                          | none => exact absurd rfl hr_nn
                          | some r0 =>
                            dsimp only at hrun'
                            have hr_not_ret : ∀ vr, r0 ≠ .returned vr := by
                              rw [evaluateHOLFiniteState_raise] at hraise; dsimp only [evalHOLExact] at hraise
                              split at hraise
                              · split at hraise <;> (injection hraise with h1 _; injection h1 with h1'; subst h1'; simp)
                              · injection hraise with h1 _; injection h1 with h1'; subst h1'; simp
                            cases r0 with
                            | returned vr => exact absurd rfl (hr_not_ret vr)
                            | _ => simp at hrun'
                      · simp at hrun'
                    · simp at hrun'
                have hne64 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 64) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                have hne184 : BitVec.ofNat 64 (globN t "ev" + off) ≠ BitVec.ofNat 64 (globN t "ev" + 184) := by
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
                  intro heq; have htn := congrArg BitVec.toNat heq
                  rcases hoff with rfl | rfl | rfl <;>
                    (rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at htn; omega)
                unfold memW; rw [hmem_ne _ hne64 hne184]
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              have hlen_res : (evmChain resumed).length = (evmChain s0).length := by
                rw [hc_res.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              have hR_lt : evmR resumed < evmR s0 := by
                rw [hc_res.2.1]; rw [hc_ce.2.1] at hR_cp; omega
              exact hcont resumed (hmeta.trans hc) hInv_res hlen_res (by simp [hR_lt])
                (hstep t cpost hInv hP hInv_cp hglob_cp (hch_cp.trans (evmChain_congr rfl rfl)) hmem_head_cp)
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact calleeBodyRun_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, _, hch_cp, hR_cp⟩ := hcg.2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩, ?_⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1, hch_cp, hc_ce.2.2.1]; exact hlen
              · rw [hc_el.2.1, hR_cp, hc_ce.2.1]; exact hR_le
              · intro _ _ _ _ _ h; cases h
            · refine calleeBodyRun_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact calleeBodyRun_error s0 cpost
          | «continue» => exact calleeBodyRun_error s0 cpost
          | finalFfi f =>
            refine calleeBodyRun_other (fun _ h => by cases h) ?_
            rintro ⟨_, h⟩; cases h
          | error => exact calleeBodyRun_error s0 cpost.emptyLocalsHOLFinite

private theorem seq_call_strict {F : Type} {s0 : PanSemStateFiniteExact 64 F}
    {P : PanSemStateFiniteExact 64 F → Prop}
    {Pc : PanSemStateFiniteExact 64 F → Prop}
    {charged : Bool}
    {fname : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64}
    {args : List (ExpHOL 64)} {cont : ProgHOL 64}
    (hlook : originalRuntimeCode.lookup fname = some (params, body, .one))
    (hentry : ∀ t values callee,
      t.code = originalRuntimeCode → EvmInv t → P t →
      evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some values →
      lookupCodeHOLFinite originalRuntimeCode.lookup fname values = some (body, callee, .one) →
      Pc (callEntryStateHOLFinite t callee))
    (hbody : CalleeBodyRun s0 Pc charged body)
    (hcont : HandlerRun s0 (fun _ => True) true cont) :
    HandlerRun s0 P charged (.seq (.call (some (none, none)) fname args) cont) := by
  intro t hc hInv hlen hR hP hnt
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
            .one ret' values callee (by rw [hc]; exact hlook) hl
        subst body'
        have hret_eq : ret' = .one := by
          have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
            t.code.lookup fname values body callee ret' hl
          rw [hc] at hx; simp only [Flapjack.lookupCodeHOLExact, hlook] at hx
          split at hx
          · exact (congrArg (fun x => x.2.2) (Option.some.inj hx)).symm
          · cases hx
        subst ret'
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
            some (body, callee, .one) := by rwa [← hc]
        have hInv_ce : EvmInv (callEntryStateHOLFinite t callee) := localsFree_evmInv t callee (t.clock - 1) hInv
        have hc_ce := evm_congr (s := t) (t := callEntryStateHOLFinite t callee) rfl rfl
        have hPc : Pc (callEntryStateHOLFinite t callee) := hentry t values callee hc hInv hP hargs hl_orig
        have hlen_ce : (evmChain (callEntryStateHOLFinite t callee)).length = (evmChain s0).length := hc_ce.2.2.1.trans hlen
        have hR_ce : if charged then evmR (callEntryStateHOLFinite t callee) < evmR s0 else evmR (callEntryStateHOLFinite t callee) ≤ evmR s0 := by
          rw [hc_ce.2.1]; exact hR
        have hmeta := (PanRunBounded.evaluateHOLFiniteState_metadata (callEntryStateHOLFinite t callee) body).1
        rcases hrun : evaluateHOLFiniteState (callEntryStateHOLFinite t callee) body with ⟨res, cpost⟩
        simp only [hrun] at hnt hmeta ⊢
        change cpost.code = t.code at hmeta
        have hB (hsafe : res ≠ some .timeOut) :
            ((∃ v, res = some (.returned v)) →
              EvmInv cpost ∧ (evmChain cpost).length = (evmChain s0).length ∧ evmR cpost < evmR s0) ∧
            (IsEvmErr res →
              EvmInv cpost ∧ (evmChain cpost).length = (evmChain s0).length ∧ evmR cpost ≤ evmR s0) := by
          have hs := hbody (callEntryStateHOLFinite t callee) hc hInv_ce hlen_ce hR_ce hPc (by rw [hrun]; exact hsafe)
          dsimp only at hs; rw [hrun] at hs; exact ⟨hs.1, hs.2.1⟩
        cases res with
        | none => exact opDispatchPost_error s0 cpost
        | some r0 =>
          cases r0 with
          | timeOut => simp at hnt
          | returned v =>
            by_cases hsh_ok : shapeEqHOL (shapeOfHOLExact v) .one = true
            · simp only [hsh_ok, ↓reduceIte] at hnt ⊢
              obtain ⟨hInv_cp, hlen_cp, hR_cp⟩ := (hB (by simp)).1 ⟨v, rfl⟩
              let resumed : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
              have hInv_res : EvmInv resumed := localsFree_evmInv cpost t.locals cpost.clock hInv_cp
              have hc_res := evm_congr (s := cpost) (t := resumed) rfl rfl
              exact hcont resumed (hmeta.trans hc) hInv_res
                (by rw [hc_res.2.2.1]; exact hlen_cp)
                (by simp only [↓reduceIte, hc_res.2.1]; exact hR_cp)
                trivial
                (by simpa [resumed] using hnt)
            · simp only [hsh_ok, Bool.false_eq_true, ↓reduceIte]
              exact opDispatchPost_error s0 cpost
          | exception eid ev =>
            by_cases heid : eid = ofString "EvmErr"
            · subst heid
              obtain ⟨hInv_cp, hlen_cp, hR_cp⟩ := (hB (by simp)).2 ⟨ev, rfl⟩
              have hInv_el : EvmInv cpost.emptyLocalsHOLFinite :=
                localsFree_evmInv cpost _ cpost.clock hInv_cp
              have hc_el := evm_congr (s := cpost) (t := cpost.emptyLocalsHOLFinite) rfl rfl
              refine ⟨?_, fun _ => ⟨hInv_el, ?_, ?_⟩⟩
              · rintro ⟨_, h⟩; cases h
              · rw [hc_el.2.2.1]; exact hlen_cp
              · rw [hc_el.2.1]; exact hR_cp
            · refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; injection h with h'; injection h' with h1 _; exact heid h1
          | «break» => exact opDispatchPost_error s0 cpost
          | «continue» => exact opDispatchPost_error s0 cpost
          | finalFfi f =>
              refine opDispatchPost_other (fun _ h => by cases h) ?_
              rintro ⟨_, h⟩; cases h
          | error => exact opDispatchPost_error s0 cpost.emptyLocalsHOLFinite

private theorem charge_with_memory_arg0_lookup {vals : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hl : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "charge_with_memory") vals =
      some (body', callee, ret')) :
    ∃ (basew : BitVec 64) (v2 v3 : ValueHOL 64),
      vals = [.val (.word basew), v2, v3] ∧
      callee.lookup (ofString "base") = some (.val (.word basew)) := by
  have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
    originalRuntimeCode.lookup (ofString "charge_with_memory") vals body' callee ret' hl
  simp only [Flapjack.lookupCodeHOLExact, lookup_charge_with_memory] at hx
  rcases vals with _ | ⟨v1, _ | ⟨v2, _ | ⟨v3, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · split at hx
    · rename_i hcond
      have heq := Option.some.inj hx
      rcases Prod.mk.inj heq with ⟨_, hrest⟩
      rcases Prod.mk.inj hrest with ⟨hloc, _⟩
      have hsh1 : shapeEqHOL .one (shapeOfHOLExact v1) = true := by
        have hs := hcond.2.2
        simp only [List.map, List.all_cons, Bool.and_eq_true, List.zip_cons_cons] at hs
        exact hs.1
      rcases v1 with ⟨⟨w1⟩⟩ | _ | _
      · refine ⟨w1, v2, v3, rfl, ?_⟩
        have hfn := congrFun hloc.symm (ofString "base")
        have hne_bs : ofString "base" ≠ ofString "start" := by decide
        have hne_bz : ofString "base" ≠ ofString "size" := by decide
        simpa [FUPDATE_LIST, FUPDATE, hne_bs, Ne.symm hne_bs, hne_bz, Ne.symm hne_bz] using hfn
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
      · simp [shapeOfHOLExact, shapeEqHOL] at hsh1
    · cases hx
  · simp at hx

private theorem charge_with_memory_body_run_of_extend_memory {F : Type}
    (s0 : PanSemStateFiniteExact 64 F)
    {Qem : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h_extend_memory : EvmPreservingSpec
      (fun s => ∃ ebw : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
        ebw.toNat < 2 ^ 37)
      Qem
      (ofString "extend_memory")) :
    CalleeBodyRun s0
      (fun t => ∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat)
      false
      (sourceFnBody Guest.Software.guestFn_charge_with_memory) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_charge_with_memory,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      (∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun _ _ _ _ _ v _ _ ⟨bw, hbw, hpos⟩ _ _ _ _ hQc => by
      obtain ⟨_, cw, ebw, rfl, heb_bounds⟩ := hQc
      have hne_xb : ofString "x" ≠ ofString "base" := by decide
      refine ⟨⟨bw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_xb, Ne.symm hne_xb, hbw], hpos⟩,
              cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨before, after, haft_lt, _, _, heb_sub, _⟩
      · decide
      · omega)
    ?_
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      (∃ totw : BitVec 64, t.locals.lookup (ofString "total") = some (.val (.word totw)) ∧ 0 < totw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    eps_add_sat_pos
    (fun t values b_as callee rs_as hc _ ⟨⟨bw, hbw, hpos⟩, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      have hb_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "base")) = some (.val (.word bw)) := hbw
      rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | u2
      · simp [hb_ev, he2] at hargs
      · simp only [hb_ev, he2, Option.some.injEq, List.cons.injEq] at hargs
        obtain ⟨hbw_eq, _⟩ := hargs
        injection hbw_eq with hbw1; injection hbw1 with hbw2; subst hbw2
        exact ⟨bw, hw1, hpos⟩)
    (fun _ _ _ _ _ v _ _ ⟨_, cw, ebw, hx, heb_lt⟩ _ _ _ _ hQc => by
      obtain ⟨_, totw, rfl, hpos⟩ := hQc
      have hne_tx : ofString "total" ≠ ofString "x" := by decide
      exact ⟨⟨totw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hpos⟩,
             cw, ebw, by simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_tx, Ne.symm hne_tx, hx], heb_lt⟩)
    ?_
  refine CalleeBodyRun.seq_charge_gas_preserves_headMem
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        ebw.toNat < 2 ^ 37)
    (fun t w hw _ ⟨⟨totw, htot, hpos⟩, _⟩ => by
      change t.locals.lookup (ofString "total") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun _ _ _ ⟨_, hx⟩ _ _ _ _ => hx)
    ?_
  refine CalleeBodyRun.seq_call
    (Q := fun _ => True)
    h_extend_memory
    (fun t values b_em callee rs_em hc _ ⟨cw, ebw, hx, heb_lt⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_lt⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (CalleeBodyRun.ret _)

private theorem charge_with_memory_body_run_aligned {F : Type}
    (s0 : PanSemStateFiniteExact 64 F) :
    CalleeBodyRun s0
      (fun t => HeadMemAligned t ∧
        ∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat)
      false
      (sourceFnBody Guest.Software.guestFn_charge_with_memory) := by
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_charge_with_memory,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ bw : BitVec 64, t.locals.lookup (ofString "base") = some (.val (.word bw)) ∧ 0 < bw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    eps_extend_memory_cost1_bounds
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ ⟨hHM, bw, hbw, hpos⟩ _ _ _ _ hQc => by
      obtain ⟨hlf, cw, ebw, rfl, heb_bounds⟩ := hQc
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "x") (.rStruct [.val (.word cw), .val (.word ebw)]) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_xb : ofString "x" ≠ ofString "base" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW ce (globN ce "ev" + 32) := by
        have hg : globN res "ev" = globN ce "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = ce.globals.lookup _; rw [hlf])
        have hm : res.memory = ce.memory := by change cpost.memory = ce.memory; rw [hlf]
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res,
              ⟨bw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_xb, Ne.symm hne_xb, hbw], hpos⟩,
              cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], ?_⟩
      rcases heb_bounds with rfl | ⟨before, after, haft_lt, haft_mod, hbef_lt, heb_sub, hbef_eq⟩
      · exact Or.inl rfl
      · right
        have hbef : before = memW ce (globN ce "ev" + 32) := hbef_eq hHM_ce.1
        have hsum : memW res (globN res "ev" + 32) + ebw.toNat = after := by
          rw [hmem32_eq, ← hbef]; omega
        rw [hsum]
        exact ⟨haft_lt, by omega, hHM_res.2⟩)
    ?_
  refine CalleeBodyRun.decCall
    (Q := fun t =>
      HeadMemAligned t ∧
      (∃ totw : BitVec 64, t.locals.lookup (ofString "total") = some (.val (.word totw)) ∧ 0 < totw.toNat) ∧
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    eps_add_sat_pos
    (fun t values b_as callee rs_as hc _ ⟨_, ⟨bw, hbw, hpos⟩, _⟩ hargs hl => by
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "add_sat") values =
          some (b_as, callee, rs_as) := by rwa [← hc]
      obtain ⟨_, _, w1, w2, rfl, hw1, _⟩ := two_word_arg_lookup (by decide) lookup_add_sat hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact] at hargs
      have hb_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.var .local (ofString "base")) = some (.val (.word bw)) := hbw
      rcases he2 : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.rfield 0 (.var .local (ofString "x"))) with _ | u2
      · simp [hb_ev, he2] at hargs
      · simp only [hb_ev, he2, Option.some.injEq, List.cons.injEq] at hargs
        obtain ⟨hbw_eq, _⟩ := hargs
        injection hbw_eq with hbw1; injection hbw1 with hbw2; subst hbw2
        exact ⟨bw, hw1, hpos⟩)
    (fun t _ _ callee _ v cpost _ ⟨hHM, _, cw, ebw, hx, heb_cond⟩ _ _ _ _ hQc => by
      obtain ⟨hlf, totw, rfl, hpos⟩ := hQc
      let ce := callEntryStateHOLFinite t callee
      have hHM_ce : HeadMemAligned ce := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost :=
        headMemAligned_congr_head_only (by rw [hlf]) (fun off _ => by unfold memW; rw [hlf]) hHM_ce
      let res := setVarHOLFinite (ofString "total") (.val (.word totw)) { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hne_tx : ofString "total" ≠ ofString "x" := by decide
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hlf]; rfl)
        have hm : res.memory = t.memory := by change cpost.memory = t.memory; rw [hlf]; rfl
        rw [hg]; unfold memW; rw [hm]
      refine ⟨hHM_res,
              ⟨totw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE], hpos⟩,
              cw, ebw, by simp [res, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne_tx, Ne.symm hne_tx, hx], ?_⟩
      rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right
        rw [hmem32_eq]
        exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine CalleeBodyRun.seq_charge_gas_preserves_headMem
    (Q := fun t =>
      ∃ cw ebw : BitVec 64,
        t.locals.lookup (ofString "x") = some (.rStruct [.val (.word cw), .val (.word ebw)]) ∧
        (ebw = 0#64 ∨
          (memW t (globN t "ev" + 32) + ebw.toNat < 2 ^ 37 ∧
           (memW t (globN t "ev" + 32) + ebw.toNat) % 8 = 0 ∧
           memW t (globN t "ev" + 24) + memW t (globN t "ev" + 40) = globN t "frame_mem_ptr")))
    (fun t w hw _ ⟨_, ⟨totw, htot, hpos⟩, _⟩ => by
      change t.locals.lookup (ofString "total") = some (.val (.word w)) at hw
      rw [htot] at hw; injection hw with hw'; injection hw' with hw''; injection hw'' with hweq; subst hweq
      exact hpos)
    (fun t cpost _ ⟨hHM, _, cw, ebw, hx, heb_cond⟩ _ hglob_cp _ hmem_head_cp => by
      have hHM_cp : HeadMemAligned cpost := headMemAligned_congr_head_only hglob_cp hmem_head_cp hHM
      let res : PanSemStateFiniteExact 64 F := { cpost with locals := t.locals }
      have hHM_res : HeadMemAligned res := headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp
      have hmem32_eq : memW res (globN res "ev" + 32) = memW t (globN t "ev" + 32) := by
        have hg : globN res "ev" = globN t "ev" := globN_eq_of_lookup_eq (by change cpost.globals.lookup _ = t.globals.lookup _; rw [hglob_cp])
        rw [hg]; exact hmem_head_cp 32 (by simp)
      refine ⟨cw, ebw, hx, ?_⟩
      rcases heb_cond with rfl | ⟨hlt37, hmod8, _⟩
      · exact Or.inl rfl
      · right
        rw [hmem32_eq]
        exact ⟨hlt37, hmod8, hHM_res.2⟩)
    ?_
  refine CalleeBodyRun.seq_call
    (Q := fun _ => True)
    eps_extend_memory_aligned
    (fun t values b_em callee rs_em hc _ ⟨cw, ebw, hx, heb_cond⟩ hargs hl => by
      have hx1 : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
          [.rfield 1 (.var .local (ofString "x"))] = some [.val (.word ebw)] := by
        rw [evalListHOLFinite_eq_toExact]
        simp [evalListHOLExact, evalHOLExact, hx]
      rw [hx1] at hargs; injection hargs with hvs; subst hvs
      have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "extend_memory") [.val (.word ebw)] =
          some (b_em, callee, rs_em) := by rwa [← hc]
      obtain ⟨_, _, ebw', heq_eb, hcal_eb⟩ := one_word_arg_lookup lookup_extend_memory hl_orig
      injection heq_eb with heq1; injection heq1 with heq2; subst heq2
      exact ⟨ebw, hcal_eb, heb_cond⟩)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
    (CalleeBodyRun.ret _)

theorem op_mload_spec_of_extend_memory
    {Qem : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop}
    (h_extend_memory : EvmPreservingSpec
      (fun s => ∃ ebw : BitVec 64,
        s.locals.lookup (ofString "expand_by") = some (.val (.word ebw)) ∧
        ebw.toNat < 2 ^ 37)
      Qem
      (ofString "extend_memory")) :
    OpHandlerSpec (ofString "op_mload") := by
  refine opHandlerSpec_of_run 510 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mload rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_mload, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine seq_call_strict
    lookup_charge_with_memory
    (fun t values callee _ _ _ hargs hl_orig => by
      obtain ⟨basew, v2, v3, rfl, hcal_base⟩ := charge_with_memory_arg0_lookup hl_orig
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact] at hargs
      rcases hst : t.locals.lookup (ofString "start") with _ | u2
      · simp [hst] at hargs
      · simp [hst] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        exact ⟨3#64, hcal_base, by decide⟩)
    (charge_with_memory_body_run_of_extend_memory s0 h_extend_memory)
    ?_
  refine HandlerRun.decCall_simple eps_sat_word ?_
  refine HandlerRun.decCall_simple eps_u256_from_be_ro ?_
  refine HandlerRun.seq_call_simple eps_stack_push ?_
  refine HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)

theorem op_mload_aligned_spec :
    FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_mload") := by
  refine ⟨_, _, _, lookup_op_mload, ?_⟩
  intro F s0 hcode ⟨hRun, hHM0⟩ _ hnt
  suffices hrun : HandlerRun s0 HeadMemAligned false (sourceFnBody Guest.Software.guestFn_op_mload) from
    hrun s0 hcode hRun.1 rfl (le_refl _) hHM0 hnt
  dsimp only [sourceFnBody, sourceFunctionEntry, Guest.Software.guestFn_op_mload,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall
    (Q := HeadMemAligned)
    eps_stack_pop_preserves_headMem
    (fun _ _ _ _ _ _ _ _ _ _ => trivial)
    (fun t _ _ callee _ v cpost _ hHM _ _ _ _ ⟨_, hHM_step⟩ => by
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      have hHM_cp : HeadMemAligned cpost := hHM_step hHM_ce
      exact headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM_cp)
    ?_
  refine seq_call_strict
    lookup_charge_with_memory
    (fun t values callee _ _ hHM hargs hl_orig => by
      obtain ⟨basew, v2, v3, rfl, hcal_base⟩ := charge_with_memory_arg0_lookup hl_orig
      have hHM_ce : HeadMemAligned (callEntryStateHOLFinite t callee) :=
        headMemAligned_congr_head_only rfl (fun _ _ => rfl) hHM
      rw [evalListHOLFinite_eq_toExact] at hargs
      simp only [evalListHOLExact, evalHOLExact] at hargs
      rcases hst : t.locals.lookup (ofString "start") with _ | u2
      · simp [hst] at hargs
      · simp [hst] at hargs
        obtain ⟨rfl, rfl, rfl⟩ := hargs
        exact ⟨hHM_ce, 3#64, hcal_base, by decide⟩)
    (charge_with_memory_body_run_aligned s0)
    ?_
  refine HandlerRun.decCall_simple eps_sat_word ?_
  refine HandlerRun.decCall_simple eps_u256_from_be_ro ?_
  refine HandlerRun.seq_call_simple eps_stack_push ?_
  refine HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
