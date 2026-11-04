import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.U256WsSpecs

/-! # OpHandlerSpec Group 01: stop & arithmetic opcodes -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

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

private theorem store_some_eq_err {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {dst val : ExpHOL 64} {res : PanSemResultExact 64}
    (h : evaluateHOLFiniteState s (.store dst val) = (some res, post)) :
    res = .error := by
  rw [evaluateHOLFiniteState_store] at h
  revert h
  rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) dst with _ | dv
  · intro h; injection h with h1; injection h1 with h2; exact h2.symm
  · cases dv with
    | val hl =>
      cases hl with
      | word addr =>
        rcases @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) val with _ | v
        · intro h; injection h with h1; injection h1 with h2; exact h2.symm
        · dsimp only
          split
          · intro h; injection h with h1; cases h1
          · intro h; injection h with h1; injection h1 with h2; exact h2.symm
    | rStruct _ => intro h; injection h with h1; injection h1 with h2; exact h2.symm
    | nStruct _ _ => intro h; injection h with h1; injection h1 with h2; exact h2.symm

theorem op_stop_spec : OpHandlerSpec (ofString "op_stop") := by
  refine opHandlerSpec_of_run 502 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_stop rfl ?_
  intro F s0 hRun
  dsimp only [Guest.Software.guestFn_op_stop, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  intro t hc hInv hlen hR _ hnt
  simp only [Bool.false_eq_true, ↓reduceIte] at hR
  have hhead_mem : (globN t "ev", globN t "cur_cont") ∈ evmChain t := by simp [evmChain, evmChainFrom]
  have hFW0 := hInv.2.choose_spec.2.2.2.2.1 _ hhead_mem
  have hb_ev := (frameWF_bounds hInv.1.2 hFW0).1
  dsimp only at hb_ev
  have hev_pos : 0 < globN t "ev" := by
    have hin := (hFW0.1 (globN t "ev", 280) (by simp)).1.1
    have h1 := hInv.1.2.2.2.1; have h2 := hInv.1.2.2.2.2.1
    rw [R11Shards.scratchStart_val] at h1; dsimp only at hin; omega
  obtain ⟨evw, hevw, hevw_nat⟩ := global_word_of_pos t "ev" hev_pos
  rw [evaluateHOLFiniteState_seq_line780] at hnt ⊢
  rcases hst : evaluateHOLFiniteState t
      (.store (.op .add [.var .global (ofString "ev"), .const 104#64]) (.const 0#64)) with ⟨r1, s1⟩
  simp only [hst] at hnt ⊢
  cases r1 with
  | some res1 =>
    have herr := store_some_eq_err hst; subst herr
    exact opDispatchPost_error s0 s1
  | none =>
    dsimp only at hnt ⊢
    obtain ⟨w1, hw1_ev, hs1_eq⟩ := store_global_off_word (t := t) (post := s1)
      (gname := "ev") (gbase := globN t "ev") (off := 104) hevw hevw_nat (by omega)
      (fun v hv => by
        simp only [evalHOLExact] at hv
        injection hv with hv'
        exact ⟨0#64, hv'.symm⟩) hst
    have hw1_zero : w1 = 0#64 := by
      simp only [evalHOLExact] at hw1_ev
      injection hw1_ev with h1; injection h1 with h2; injection h2 with h3
      exact h3.symm
    subst hw1_zero
    have hGs1 : GuestInv s1 := guestInv_congr (s := t)
      (by simp [hs1_eq]) (by simp [hs1_eq]) (by simp [hs1_eq]) (by simp [hs1_eq]) hInv.1.1
    have hglob_s1 : s1.globals = t.globals := by simp [hs1_eq]
    have hbe_s1 : s1.be = t.be := by simp [hs1_eq]
    have hcode_s1 : s1.code = originalRuntimeCode := by rw [hs1_eq]; exact hc
    have hmem_out_s1 : ∀ x : BitVec 64,
        (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN t "ev" + off)) →
        s1.memory x = t.memory x := by
      intro x hx
      rw [hs1_eq]; dsimp only [updW]
      rw [if_neg (hx 104 (by simp [nonStructFrameOffs]))]
    obtain ⟨hInv_s1, hch_s1, hR_s1⟩ := evmInv_of_head_nonstruct hInv hGs1 hglob_s1 hbe_s1 hmem_out_s1
    have hm104_s1 : memW s1 (globN t "ev" + 104) = 0 := by
      rw [hs1_eq]; simpa using memW_updW_same t (globN t "ev" + 104) 0#64
    -- Now step through `call (some (none, none)) "pc_add" [1]`
    rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_call] at hnt ⊢
    have hargs : evalListHOLFinite s1 (h := fun a => Classical.propDecidable (s1.memaddrs a)) [.const 1#64] =
        some [.val (.word 1#64)] := by
      rw [evalListHOLFinite_eq_toExact]; rfl
    simp only [hargs] at hnt ⊢
    rcases hl : lookupCodeHOLFinite s1.code.lookup (ofString "pc_add") [.val (.word 1#64)] with _ | ⟨body', callee, ret'⟩
    · exact opDispatchPost_error s0 s1
    · simp only [hl] at hnt ⊢
      by_cases hz : s1.clock = 0
      · simp [hz] at hnt
      · simp only [hz, ↓reduceIte] at hnt ⊢
        have hl_orig : lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "pc_add") [.val (.word 1#64)] =
            some (body', callee, ret') := by rwa [← hcode_s1]
        obtain ⟨rfl, rfl, _, _, _⟩ := one_word_arg_lookup lookup_pc_add hl_orig
        have hbody_pc : sourceFnBody Guest.Software.guestFn_pc_add =
            .seq
              (.store (.op .add [.var .global (ofString "ev"), .const 0])
                (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")]))
              (.return (.const 0)) := rfl
        let ce := callEntryStateHOLFinite s1 callee
        have hInv_ce : EvmInv ce := localsFree_evmInv s1 callee (s1.clock - 1) hInv_s1
        have hevw_ce : ce.globals.lookup (ofString "ev") = some (.val (.word evw)) := by
          change s1.globals.lookup (ofString "ev") = _; rw [hglob_s1]; exact hevw
        rw [hbody_pc, evaluateHOLFiniteState_seq_line780] at hnt ⊢
        rcases hst_pc : evaluateHOLFiniteState ce
            (.store (.op .add [.var .global (ofString "ev"), .const 0])
              (.op .add [.load .one (.op .add [.var .global (ofString "ev"), .const 0]), .var .local (ofString "n")])) with ⟨rpc, spc⟩
        simp only [hst_pc] at hnt ⊢
        cases rpc with
        | some res_pc =>
          have herr_pc := store_some_eq_err hst_pc; subst herr_pc
          dsimp only at hnt ⊢
          exact opDispatchPost_error s0 spc.emptyLocalsHOLFinite
        | none =>
          dsimp only at hnt ⊢
          obtain ⟨wpc, _, hspc_eq⟩ := store_global_off_word (t := ce) (post := spc)
            (gname := "ev") (gbase := globN t "ev") (off := 0) hevw_ce hevw_nat (by omega)
            (fun v hv => by
              simp only [evalHOLExact, wordOpHOL] at hv; revert hv
              rcases @evalListHOLExact 64 F _ ce.toExact (fun a => Classical.propDecidable (ce.memaddrs a)) _ with _ | vs
              · simp
              · dsimp only; split
                · simp only [Option.map]
                  rcases wordOp .add (vs.map valueWord) with _ | w
                  · simp
                  · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
                · simp) hst_pc
          rw [evaluateHOLFiniteState_return]
          dsimp only [evalHOLExact]
          have hsz0 : sizeOfShapeWithContextHOL spc.structs
              (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0]
          dsimp only
          have hsh0 : shapeEqHOL (shapeOfHOLExact (.val (.word (0 : BitVec 64)) : ValueHOL 64)) .one = true := by
            simp [shapeEqHOL, shapeOfHOLExact]
          simp only [hsh0, ↓reduceIte]
          let s2 : PanSemStateFiniteExact 64 F := { (emptyLocalsHOLFinite spc) with locals := s1.locals }
          rw [evaluateHOLFiniteState_return]
          dsimp only [evalHOLExact]
          have hsz0_s2 : sizeOfShapeWithContextHOL s2.structs
              (shapeOfHOLExact (.val (.word (0#64 : BitVec 64)))) ≤ 32 := by
            simp [shapeOfHOLExact, sizeOfShapeWithContextHOL]
          rw [if_pos hsz0_s2]
          dsimp only
          let post := emptyLocalsHOLFinite s2
          have hGpost : GuestInv post := guestInv_congr (s := t)
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            (by simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq])
            hInv.1.1
          have hglob_post : post.globals = t.globals := by
            simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq]
          have hbe_post : post.be = t.be := by
            simp [post, s2, emptyLocalsHOLFinite, hspc_eq, ce, callEntryStateHOLFinite, hs1_eq]
          have hmem_out_post : ∀ x : BitVec 64,
              (∀ off ∈ nonStructFrameOffs, x ≠ BitVec.ofNat 64 (globN t "ev" + off)) →
              post.memory x = t.memory x := by
            intro x hx
            change spc.memory x = t.memory x
            rw [hspc_eq]; dsimp only [updW]
            rw [if_neg (hx 0 (by simp [nonStructFrameOffs]))]
            exact hmem_out_s1 x hx
          obtain ⟨hInv_post, hch_post, hR_post⟩ :=
            evmInv_of_head_nonstruct hInv hGpost hglob_post hbe_post hmem_out_post
          have hDone_post : EvmDone post := by
            right; left
            have hgev : globN post "ev" = globN t "ev" := by simp [globN, hglob_post]
            rw [hgev]
            change memW spc (globN t "ev" + 104) = 0
            rw [hspc_eq, memW_updW_ne ce (globN t "ev" + 0) (globN t "ev" + 104) wpc (by omega) (by omega) (by omega)]
            exact hm104_s1
          have hpot_lt : evmPot post < evmPot s0 :=
            evmPot_lt_of_done hRun hInv_post hDone_post
              (by rw [hch_post, hlen]) (by rw [hR_post]; exact hR)
          refine ⟨fun _ => ⟨hInv_post, hpot_lt⟩, ?_⟩
          rintro ⟨_, h⟩; cases h

theorem op_add_spec : OpHandlerSpec (ofString "op_add") := by
  refine opHandlerSpec_of_run 475 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_add rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_add, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_add
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_mul_spec : OpHandlerSpec (ofString "op_mul") := by
  refine opHandlerSpec_of_run 476 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mul rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_mul, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_mul
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_sub_spec : OpHandlerSpec (ofString "op_sub") := by
  refine opHandlerSpec_of_run 477 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sub rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_sub, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_sub
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_div_spec : OpHandlerSpec (ofString "op_div") := by
  refine opHandlerSpec_of_run 478 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_div rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_div, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_div
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_sdiv_spec : OpHandlerSpec (ofString "op_sdiv") := by
  refine opHandlerSpec_of_run 479 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sdiv rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_sdiv, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_sdiv
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_mod_spec : OpHandlerSpec (ofString "op_mod") := by
  refine opHandlerSpec_of_run 480 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mod rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_mod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_mod
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_smod_spec : OpHandlerSpec (ofString "op_smod") := by
  refine opHandlerSpec_of_run 481 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_smod rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_smod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_u256_smod
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _))))))

theorem op_addmod_spec : OpHandlerSpec (ofString "op_addmod") := by
  refine opHandlerSpec_of_run 482 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_addmod rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_addmod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.decCall_simple eps_stack_pop
          (HandlerRun.seq_charge_gas_const (by decide)
            (HandlerRun.decCall_simple eps_u256_addmod
              (HandlerRun.seq_call_simple eps_stack_push
                (HandlerRun.seq_call_simple eps_pc_add
                  (HandlerRun.ret _)))))))

theorem op_mulmod_spec : OpHandlerSpec (ofString "op_mulmod") := by
  refine opHandlerSpec_of_run 483 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_mulmod rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_mulmod, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.decCall_simple eps_stack_pop
          (HandlerRun.seq_charge_gas_const (by decide)
            (HandlerRun.decCall_simple eps_u256_mulmod
              (HandlerRun.seq_call_simple eps_stack_push
                (HandlerRun.seq_call_simple eps_pc_add
                  (HandlerRun.ret _)))))))

theorem op_exp_spec : OpHandlerSpec (ofString "op_exp") := by
  refine opHandlerSpec_of_run 484 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_exp rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_exp, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRun.decCall_simple eps_stack_pop
    (HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall
        (Q := fun t => ∃ nbw : BitVec 64, t.locals.lookup (ofString "nb") = some (.val (.word nbw)) ∧ nbw.toNat ≤ 32)
        eps_u256_byte_length_le32
        (fun _ _ _ _ _ _ _ _ _ _ => trivial)
        (fun t _ _ _ _ v cpost _ _ _ _ _ _ hQc => by
          obtain ⟨_, nbw, rfl, hle⟩ := hQc
          exact ⟨nbw, by simp [setVarHOLFinite, FUPDATE], hle⟩)
        (HandlerRun.seq_charge_gas
          (Q := fun _ => True)
          (fun t w hw _ ⟨nbw, hnb, hle⟩ => by
            have hev_amt : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
                (.op .add [.const 10#64, .panop .mul [.const 50#64, .var .local (ofString "nb")]]) =
                some (.val (.word (10#64 + 50#64 * nbw))) := by
              simp [evalHOLExact, evalListHOLExact, hnb, wordOpHOL, wordOp, panOpHOL, valueIsWord, valueWord]
            rw [hev_amt] at hw
            injection hw with h1; injection h1 with h2; injection h2 with h3
            subst h3
            have hmul : (50#64 * nbw).toNat = 50 * nbw.toNat := by
              rw [BitVec.toNat_mul, show (50#64 : BitVec 64).toNat = 50 by decide, Nat.mod_eq_of_lt (by omega)]
            rw [BitVec.toNat_add, show (10#64 : BitVec 64).toNat = 10 by decide, hmul,
                Nat.mod_eq_of_lt (by omega)]
            omega)
          (fun _ _ _ _ _ _ _ => trivial)
          (HandlerRun.decCall_simple eps_u256_exp
            (HandlerRun.seq_call_simple eps_stack_push
              (HandlerRun.seq_call_simple eps_pc_add
                (HandlerRun.ret _)))))))

theorem op_signextend_spec : OpHandlerSpec (ofString "op_signextend") := by
  refine opHandlerSpec_of_run 485 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_signextend rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_signextend, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.seq_charge_gas_const (by decide)
          (HandlerRun.decCall_simple eps_sat_word
            (HandlerRun.decCall_simple eps_u256_signextend
              (HandlerRun.seq_call_simple eps_stack_push
                (HandlerRun.seq_call_simple eps_pc_add
                  (HandlerRun.ret _)))))))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
