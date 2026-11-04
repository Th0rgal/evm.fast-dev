import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group06ControlFlow
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group07Transient
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.WarmAccessHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadDelHtabSet
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.StateGasHelpers

/-! # OpHandlerSpec Group 07b: State, Account, Storage & Selfdestruct Opcodes

Proves:
- Pre-`C00` world/account callee contract bundle `WorldAccountSpecs`
- `OpHandlerSpec` (given `WorldAccountSpecs`) for the 7 state/account/storage/selfdestruct opcodes:
  `op_balance`, `op_selfbalance`, `op_extcodesize`, `op_extcodehash`,
  `op_sload`, `op_sstore`, `op_selfdestruct`
-/

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

/-! ## 1. Pre-`C00` world/account callee contract bundle -/

structure WorldAccountSpecs : Prop where
  eps_get_account :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_account")
  eps_ext_code_of :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "ext_code_of")
  eps_get_storage :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage")
  eps_get_storage_original :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage_original")
  eps_set_storage :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")
  eps_is_account_alive :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "is_account_alive")
  eps_move_ether :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "move_ether")
  eps_emit_transfer_log :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "emit_transfer_log")

/-! ## 2. `OpHandlerSpec` proofs for the 7 state/account/storage/selfdestruct opcodes -/

private theorem word_local_pos_of_lookup {F : Type} (t : PanSemStateFiniteExact 64 F)
    (nm : MlS) {v : ValueHOL 64}
    (heval : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.var .local nm) = some v)
    {cw : BitVec 64} (hlk : t.locals.lookup nm = some (.val (.word cw))) :
    v = .val (.word cw) := by
  simpa [evalHOLExact, hlk] using heval.symm

theorem op_selfbalance_spec (hW : WorldAccountSpecs) :
    OpHandlerSpec (ofString "op_selfbalance") := by
  refine opHandlerSpec_of_run 549 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_selfbalance rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_selfbalance, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  exact
    HandlerRun.seq_charge_gas_const (by decide)
      (HandlerRun.decCall_simple hW.eps_get_account
        (HandlerRun.seq_call_simple eps_stack_push
          (HandlerRun.seq_call_simple eps_pc_add
            (HandlerRun.ret _))))

theorem op_balance_spec (hW : WorldAccountSpecs) :
    OpHandlerSpec (ofString "op_balance") := by
  refine opHandlerSpec_of_run 532 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_balance rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_balance, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_to_address_masked
        (HandlerRun.decCall (Q := fun t => ∃ cw : BitVec 64,
            t.locals.lookup (ofString "c") = some (.val (.word cw)) ∧ 0 < cw.toNat)
          eps_access_gas_cost_bounds
          (fun _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ v _ _ _ _ _ _ _ ⟨_, cw, hv, hcw⟩ => by
            subst hv
            refine ⟨cw, ?_, by rcases hcw with h | h <;> omega⟩
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          (HandlerRun.seq_charge_gas (Q := fun _ => True)
            (fun t w hw _ ⟨cw, hlk, hpos⟩ => by
              have heq := word_local_pos_of_lookup t (ofString "c") hw hlk
              injection heq with h1; injection h1 with h2; subst h2; exact hpos)
            (fun _ _ _ _ _ _ _ => trivial)
            (HandlerRun.seq_call_simple eps_warm_after_charge
              (HandlerRun.decCall_simple hW.eps_get_account
                (HandlerRun.seq_call_simple eps_stack_push
                  (HandlerRun.seq_call_simple eps_pc_add
                    (HandlerRun.ret _))))))))

theorem op_extcodesize_spec (hW : WorldAccountSpecs) :
    OpHandlerSpec (ofString "op_extcodesize") := by
  refine opHandlerSpec_of_run 544 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_extcodesize rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_extcodesize, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_to_address_masked
        (HandlerRun.decCall (Q := fun t => ∃ cw : BitVec 64,
            t.locals.lookup (ofString "c") = some (.val (.word cw)) ∧
            (cw.toNat = 100 ∨ cw.toNat = 3000))
          eps_access_gas_cost_bounds
          (fun _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ v _ _ _ _ _ _ _ ⟨_, cw, hv, hcw⟩ => by
            subst hv
            refine ⟨cw, ?_, hcw⟩
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          (HandlerRun.seq_charge_gas (Q := fun _ => True)
            (fun t w hw _ ⟨cw, hlk, hcw⟩ => by
              simp only [evalHOLExact, evalListHOLExact, hlk, wordOpHOL, wordOp, valueIsWord, valueWord,
                List.all, List.map, Option.map, Bool.and_self, ↓reduceIte,
                List.foldr, BitVec.add_zero] at hw
              injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3
              subst hw3
              have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
              have h100 : (100#64 + (0 : BitVec 64)).toNat = 100 := rfl
              rw [BitVec.toNat_add, h100]
              rcases hcw with h | h <;> omega)
            (fun _ _ _ _ _ _ _ => trivial)
            (HandlerRun.seq_call_simple eps_warm_after_charge
              (HandlerRun.decCall_simple hW.eps_ext_code_of
                (HandlerRun.seq_call_simple eps_stack_push_word
                  (HandlerRun.seq_call_simple eps_pc_add
                    (HandlerRun.ret _))))))))

theorem op_extcodehash_spec (hW : WorldAccountSpecs) :
    OpHandlerSpec (ofString "op_extcodehash") := by
  refine opHandlerSpec_of_run 548 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_extcodehash rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_extcodehash, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.decCall_simple eps_to_address_masked
        (HandlerRun.decCall (Q := fun t => ∃ cw : BitVec 64,
            t.locals.lookup (ofString "c") = some (.val (.word cw)) ∧ 0 < cw.toNat)
          eps_access_gas_cost_bounds
          (fun _ _ _ _ _ _ _ _ _ _ => trivial)
          (fun _ _ _ _ _ v _ _ _ _ _ _ _ ⟨_, cw, hv, hcw⟩ => by
            subst hv
            refine ⟨cw, ?_, by rcases hcw with h | h <;> omega⟩
            simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
          (HandlerRun.seq_charge_gas (Q := fun _ => True)
            (fun t w hw _ ⟨cw, hlk, hpos⟩ => by
              have heq := word_local_pos_of_lookup t (ofString "c") hw hlk
              injection heq with h1; injection h1 with h2; subst h2; exact hpos)
            (fun _ _ _ _ _ _ _ => trivial)
            (HandlerRun.seq_call_simple eps_warm_after_charge
              (HandlerRun.decCall_simple hW.eps_get_account
                (HandlerRun.decCall_simple eps_acct_is_empty_ro
                  (HandlerRun.seq_ite_unit
                    (fun _ _ _ _ =>
                      HandlerRun.seq_call_simple eps_stack_push
                        (HandlerRun.seq_call_simple eps_pc_add
                          (HandlerRun.ret _)))
                    (fun _ _ =>
                      HandlerRun.seq_decCall_call eps_u256_from_be_ro eps_stack_push
                        (fun _ _ _ _ _ _ _ _ _ _ => trivial)
                        (fun _ _ _ _ _ _ _ _ _ => trivial)
                        (fun _ _ _ _ _ _ _ => trivial)
                        (HandlerRun.seq_call_simple eps_pc_add
                          (HandlerRun.ret _))))))))))

theorem htab_set_head_del_callee_t {F : Type}
    (t : PanSemStateFiniteExact 64 F) (hInv : EvmInv t) (hc : t.code = originalRuntimeCode)
    {keyVar : MlS}
    {values : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]),
       .var .local keyVar, .const (BitVec.ofNat 64 1)] = some values)
    (hl : lookupCodeHOLFinite t.code.lookup (ofString "htab_set") values =
      some (body', callee, ret')) :
    locN (callEntryStateHOLFinite t callee) "t" =
      memW (callEntryStateHOLFinite t callee) (globN (callEntryStateHOLFinite t callee) "ev" + 136) := by
  obtain ⟨hb_ev, evw, hevw, hevw_nat⟩ := ev_word_bounds hInv
  rw [evalListHOLFinite_eq_toExact] at hargs
  unfold evalListHOLExact at hargs
  rcases ht_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.load .one (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)])) with _ | vt
  · rw [ht_ev] at hargs; simp at hargs
  · rw [ht_ev] at hargs
    unfold evalListHOLExact at hargs
    rcases hk_ev : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.var .local keyVar) with _ | vk
    · rw [hk_ev] at hargs; simp at hargs
    · rw [hk_ev] at hargs
      unfold evalListHOLExact at hargs
      dsimp only [evalHOLExact] at hargs
      injection hargs with hv_eq
      subst hv_eq
      have had_eq : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
          (.op .add [.var .global (ofString "ev"), .const (BitVec.ofNat 64 136)]) =
          some (.val (.word (BitVec.ofNat 64 (globN t "ev" + 136)))) := by
        simp only [evalHOLExact, evalListHOLExact, hevw, wordOpHOL, wordOp, valueIsWord, valueWord,
          List.all, List.map, Option.map, Bool.and_self, ↓reduceIte, List.foldr, BitVec.add_zero]
        congr 3
        apply BitVec.eq_of_toNat_eq
        have hz0 : (0 : BitVec 64).toNat = 0 := rfl
        have h264 : (2 ^ 64 : Nat) = 18446744073709551616 := by norm_num
        simp only [BitVec.toNat_add, BitVec.toNat_ofNat, hevw_nat, hz0, Nat.add_zero,
          Nat.mod_eq_of_lt (show 136 < 2 ^ 64 by omega),
          Nat.mod_eq_of_lt (show globN t "ev" + 136 < 2 ^ 64 by omega)]
      unfold evalHOLExact at ht_ev
      rw [had_eq] at ht_ev; dsimp only at ht_ev
      unfold memLoadHOLExact at ht_ev
      have hvt_w : ∃ tw : BitVec 64, vt = .val (.word tw) ∧ tw.toNat = memW t (globN t "ev" + 136) := by
        split at ht_ev
        · split at ht_ev
          · injection ht_ev with htw_m
            unfold memW
            cases hm_cell : t.memory (BitVec.ofNat 64 (globN t "ev" + 136)) with
            | word cw =>
              change ValueHOL.val (t.memory (BitVec.ofNat 64 (globN t "ev" + 136))) = vt at htw_m
              rw [hm_cell] at htw_m
              exact ⟨cw, htw_m.symm, rfl⟩
          · cases ht_ev
        · cases ht_ev
      obtain ⟨tw, rfl, htw_nat⟩ := hvt_w
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
        t.code.lookup (ofString "htab_set") [.val (.word tw), vk, .val (.word 1)] body' callee ret' hl
      rw [hc] at hx
      simp only [Flapjack.lookupCodeHOLExact, SoloHtabSet.lookup_htab_set] at hx
      split at hx
      · have hmap := congrArg (fun x => x.2.1) (Option.some.inj hx)
        have hcal_t : callee.lookup (ofString "t") = some (.val (.word tw)) := by
          have := congrFun hmap.symm (ofString "t")
          have h1 : ofString "t" ≠ ofString "value" := by decide
          have h2 : ofString "t" ≠ ofString "key" := by decide
          have h3 : ofString "value" ≠ ofString "t" := by decide
          have h4 : ofString "key" ≠ ofString "t" := by decide
          simpa [List.map, List.zip, List.foldl, FUPDATE_LIST, FUPDATE, h1, h2, h3, h4] using this
        simp [callEntryStateHOLFinite, locN, hcal_t, htw_nat, memW, globN]
      · cases hx

theorem op_sload_spec (hW : WorldAccountSpecs) :
    OpHandlerSpec (ofString "op_sload") := by
  refine opHandlerSpec_of_run 527 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sload rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_sload, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.dec (Q := fun t => locN t "key" = globN t "evm_key_buf")
        (fun t v hv _ _ => dec_key_evm_key_buf_eq t v hv)
        (HandlerRun.seq_call (Q := fun _ => True)
          eps_u256_to_be32_evm_key_buf
          (fun t _ _ _ _ hc _ hkey hargs hl =>
            u256_to_be32_callee_out_eq_key t hc hkey hargs hl)
          (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
          (HandlerRun.dec_simple
            (HandlerRun.decCall_simple eps_is_warm_storage_key
              (HandlerRun.seq_ite_unit
                (fun _ _ _ _ =>
                  HandlerRun.seq_charge_gas_const (by decide)
                    (HandlerRun.decCall_simple hW.eps_get_storage
                      (HandlerRun.seq_call_simple eps_stack_push
                        (HandlerRun.seq_call_simple eps_pc_add
                          (HandlerRun.ret _)))))
                (fun _ _ =>
                  HandlerRun.seq_assoc
                    (HandlerRun.seq_charge_gas_const (by decide)
                      (HandlerRun.seq_call_simple eps_warm_storage_key
                        (HandlerRun.decCall_simple hW.eps_get_storage
                          (HandlerRun.seq_call_simple eps_stack_push
                            (HandlerRun.seq_call_simple eps_pc_add
                              (HandlerRun.ret _))))))))))))

theorem op_sstore_spec (hW : WorldAccountSpecs) :
    OpHandlerSpec (ofString "op_sstore") := by
  refine opHandlerSpec_of_run 528 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_sstore rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_sstore, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  refine HandlerRun.seq_call_simple eps_require_not_static ?_
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.dec (Q := fun t => locN t "key" = globN t "evm_key_buf")
    (fun t v hv _ _ => dec_key_evm_key_buf_eq t v hv) ?_
  refine HandlerRun.seq_call (Q := fun _ => True)
    eps_u256_to_be32_evm_key_buf
    (fun t _ _ _ _ hc _ hkey hargs hl =>
      u256_to_be32_callee_out_eq_key t hc hkey hargs hl)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial) ?_
  refine HandlerRun.dec_simple ?_
  refine HandlerRun.decCall_simple eps_is_warm_storage_key ?_
  refine HandlerRun.dec (Q := fun t => ∃ cw : BitVec 64,
      t.locals.lookup (ofString "access_cost") = some (.val (.word cw)) ∧ 0 < cw.toNat)
    (fun _ v hv _ _ => by
      change some (ValueHOL.val (.word 100#64)) = some v at hv
      injection hv with hv'
      subst hv'
      refine ⟨100#64, ?_, by decide⟩
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ?_
  refine HandlerRun.seq_ite_unit
    (fun _ _ _ _ =>
      HandlerRun.seq_assign_local
        (Q := fun t => ∃ cw : BitVec 64,
          t.locals.lookup (ofString "access_cost") = some (.val (.word cw)) ∧ 0 < cw.toNat)
        (fun _ v hv _ _ => by
          change some (ValueHOL.val (.word 2100#64)) = some v at hv
          injection hv with hv'
          subst hv'
          refine ⟨2100#64, ?_, by decide⟩
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        ?_)
    (fun _ _ => HandlerRun.seq_skip ?_)
  all_goals
    refine HandlerRun.decCall (Q := fun t => ∃ cw : BitVec 64,
        t.locals.lookup (ofString "access_cost") = some (.val (.word cw)) ∧ 0 < cw.toNat)
      eps_max
      (fun _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ ⟨cw, hlk, hpos⟩ _ _ _ _ _ => by
        refine ⟨cw, ?_, hpos⟩
        have hne : ofString "mx" ≠ ofString "access_cost" := by decide
        have hne' : ofString "access_cost" ≠ ofString "mx" := by decide
        simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, hne'] using hlk) ?_
    refine HandlerRun.seq_call (Q := fun t => ∃ cw : BitVec 64,
        t.locals.lookup (ofString "access_cost") = some (.val (.word cw)) ∧ 0 < cw.toNat)
      eps_check_gas
      (fun _ _ _ _ _ _ _ _ _ _ => trivial)
      (fun _ _ _ _ _ _ _ _ hP _ _ _ _ _ => hP) ?_
    refine HandlerRun.seq_charge_gas (Q := fun _ => True)
      (fun t w hw _ ⟨cw, hlk, hpos⟩ => by
        have heq := word_local_pos_of_lookup t (ofString "access_cost") hw hlk
        injection heq with h1; injection h1 with h2; subst h2; exact hpos)
      (fun _ _ _ _ _ _ _ => trivial) ?_
    refine HandlerRun.seq_ite_unit
      (fun _ _ _ _ => HandlerRun.seq_call_simple eps_warm_storage_key ?_)
      (fun _ _ => HandlerRun.seq_skip ?_)
    all_goals
      refine HandlerRun.decCall_simple hW.eps_get_storage_original ?_
      refine HandlerRun.decCall_simple hW.eps_get_storage ?_
      refine HandlerRun.decCall_simple eps_u256_eq_ro ?_
      refine HandlerRun.decCall_simple eps_u256_eq_ro ?_
      refine HandlerRun.decCall_simple eps_u256_eq_ro ?_
      refine HandlerRun.decCall_simple eps_u256_is_zero_ro ?_
      refine HandlerRun.decCall_simple eps_u256_is_zero_ro ?_
      refine HandlerRun.decCall_simple eps_u256_is_zero_ro ?_
      refine HandlerRun.dec_simple ?_
      have hev96_val : ∀ (op : BinOp) (c : BitVec 64) (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64),
          True →
          @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
            (.op op [.load .one (.op .add [.var .global (ofString "ev"), .const 96]), .const c]) = some v →
          ∃ w : BitVec 64, v = .val (.word w) := by
        intro op c t v _ hv
        simp only [evalHOLExact, wordOpHOL] at hv
        revert hv
        rcases @evalListHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) _ with _ | vs
        · simp
        · dsimp only
          split
          · simp only [Option.map]
            rcases wordOp op (vs.map valueWord) with _ | w
            · simp
            · intro hv; injection hv with hv'; exact ⟨w, hv'.symm⟩
          · simp
      refine HandlerRun.seq_ite_unit
        (fun _ _ _ _ => HandlerRun.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial) ?_)
        (fun _ _ => HandlerRun.seq_skip ?_)
      all_goals
        refine HandlerRun.seq_ite_unit
          (fun _ _ _ _ =>
            HandlerRun.seq_assoc
              (HandlerRun.seq_ite_unit
                (fun _ _ _ _ =>
                  HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True) 96 (by simp [nonStructFrameOffs])
                    (hev96_val .add 11616) (fun _ _ _ _ _ => trivial) ?_)
                (fun _ _ => HandlerRun.seq_skip ?_)))
          (fun _ _ => HandlerRun.seq_skip ?_)
        · refine HandlerRun.seq_assoc
            (HandlerRun.seq_ite_unit
              (fun _ _ _ _ =>
                HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True) 96 (by simp [nonStructFrameOffs])
                  (hev96_val .sub 11616) (fun _ _ _ _ _ => trivial) ?_)
              (fun _ _ => HandlerRun.seq_skip ?_))
          all_goals
            refine HandlerRun.seq_ite_unit
              (fun _ _ _ _ =>
                HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True) 96 (by simp [nonStructFrameOffs])
                  (hev96_val .add 10000) (fun _ _ _ _ _ => trivial) ?_)
              (fun _ _ => HandlerRun.seq_skip ?_)
            all_goals
              refine HandlerRun.dec_simple ?_
              refine HandlerRun.seq_ite_unit
                (fun _ _ _ _ => HandlerRun.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial) ?_)
                (fun _ _ => HandlerRun.seq_skip ?_)
              all_goals
                exact HandlerRun.seq_ite_unit
                  (fun _ _ _ _ =>
                    HandlerRun.seq_call_simple eps_credit_state_gas_refund
                      (HandlerRun.seq_call_simple eps_charge_gas_any
                        (HandlerRun.seq_call_simple eps_charge_state_gas
                          (HandlerRun.seq_call_simple hW.eps_set_storage
                            (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))))))
                  (fun _ _ =>
                    HandlerRun.seq_skip
                      (HandlerRun.seq_call_simple eps_charge_gas_any
                        (HandlerRun.seq_call_simple eps_charge_state_gas
                          (HandlerRun.seq_call_simple hW.eps_set_storage
                            (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))))))
        · refine HandlerRun.seq_assoc
            (HandlerRun.seq_ite_unit
              (fun _ _ _ _ =>
                HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True) 96 (by simp [nonStructFrameOffs])
                  (hev96_val .sub 11616) (fun _ _ _ _ _ => trivial) ?_)
              (fun _ _ => HandlerRun.seq_skip ?_))
          all_goals
            refine HandlerRun.seq_ite_unit
              (fun _ _ _ _ =>
                HandlerRun.seq_store_ev_nonstruct (Q := fun _ => True) 96 (by simp [nonStructFrameOffs])
                  (hev96_val .add 10000) (fun _ _ _ _ _ => trivial) ?_)
              (fun _ _ => HandlerRun.seq_skip ?_)
            all_goals
              refine HandlerRun.dec_simple ?_
              refine HandlerRun.seq_ite_unit
                (fun _ _ _ _ => HandlerRun.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial) ?_)
                (fun _ _ => HandlerRun.seq_skip ?_)
              all_goals
                exact HandlerRun.seq_ite_unit
                  (fun _ _ _ _ =>
                    HandlerRun.seq_call_simple eps_credit_state_gas_refund
                      (HandlerRun.seq_call_simple eps_charge_gas_any
                        (HandlerRun.seq_call_simple eps_charge_state_gas
                          (HandlerRun.seq_call_simple hW.eps_set_storage
                            (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))))))
                  (fun _ _ =>
                    HandlerRun.seq_skip
                      (HandlerRun.seq_call_simple eps_charge_gas_any
                        (HandlerRun.seq_call_simple eps_charge_state_gas
                          (HandlerRun.seq_call_simple hW.eps_set_storage
                            (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))))))
        · refine HandlerRun.dec_simple ?_
          refine HandlerRun.seq_ite_unit
            (fun _ _ _ _ => HandlerRun.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial) ?_)
            (fun _ _ => HandlerRun.seq_skip ?_)
          all_goals
            exact HandlerRun.seq_ite_unit
              (fun _ _ _ _ =>
                HandlerRun.seq_call_simple eps_credit_state_gas_refund
                  (HandlerRun.seq_call_simple eps_charge_gas_any
                    (HandlerRun.seq_call_simple eps_charge_state_gas
                      (HandlerRun.seq_call_simple hW.eps_set_storage
                        (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))))))
              (fun _ _ =>
                HandlerRun.seq_skip
                  (HandlerRun.seq_call_simple eps_charge_gas_any
                    (HandlerRun.seq_call_simple eps_charge_state_gas
                      (HandlerRun.seq_call_simple hW.eps_set_storage
                        (HandlerRun.seq_call_simple eps_pc_add (HandlerRun.ret _))))))

theorem op_selfdestruct_spec (hW : WorldAccountSpecs) :
    OpHandlerSpec (ofString "op_selfdestruct") := by
  refine opHandlerSpec_of_run 570 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_selfdestruct rfl ?_
  intro F s0 hRun
  dsimp only [Guest.Software.guestFn_op_selfdestruct, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeListToHOLStructural,
    List.map, Option.map]
  refine HandlerRun.seq_call_simple eps_require_not_static ?_
  refine HandlerRun.decCall_simple eps_stack_pop ?_
  refine HandlerRun.decCall_simple eps_to_address_masked ?_
  refine HandlerRun.decCall_simple eps_is_warm_address_ro ?_
  refine HandlerRun.dec (Q := fun t =>
      t.locals.lookup (ofString "gas_cost") = some (.val (.word 5000#64)))
    (fun _ v hv _ _ => by
      change some (ValueHOL.val (.word 5000#64)) = some v at hv
      injection hv with hv'; subst hv'
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ?_
  refine HandlerRun.seq_ite_unit
    (fun _ _ _ _ =>
      HandlerRun.seq_assign_local
        (Q := fun t => ∃ gw : BitVec 64,
          t.locals.lookup (ofString "gas_cost") = some (.val (.word gw)) ∧ 0 < gw.toNat)
        (fun t v hv _ hlk => by
          simp [evalHOLExact, evalListHOLExact, hlk, wordOpHOL, wordOp, valueIsWord, valueWord] at hv
          subst hv
          refine ⟨8000#64, ?_, by decide⟩
          simp [setKvarHOLFinite, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE])
        ?_)
    (fun _ _ =>
      HandlerRun.seq_skip
        (HandlerRun.weaken
          (Q := fun t => ∃ gw : BitVec 64,
            t.locals.lookup (ofString "gas_cost") = some (.val (.word gw)) ∧ 0 < gw.toNat)
          (fun _ _ hlk => ⟨5000#64, hlk, by decide⟩) ?_))
  all_goals
    refine HandlerRun.seq_charge_gas (Q := fun _ => True)
      (fun t w hw _ ⟨gw, hlk, hpos⟩ => by
        have heq := word_local_pos_of_lookup t (ofString "gas_cost") hw hlk
        injection heq with h1; injection h1 with h2; subst h2
        exact hpos)
      (fun _ _ _ _ _ _ _ => trivial) ?_
    refine HandlerRun.seq_ite_unit
      (fun _ _ _ _ => HandlerRun.seq_call_simple eps_warm_address ?_)
      (fun _ _ => HandlerRun.seq_skip ?_)
    all_goals
      refine HandlerRun.dec_simple ?_
      refine HandlerRun.decCall_simple hW.eps_is_account_alive ?_
      refine HandlerRun.decCall_simple hW.eps_get_account ?_
      refine HandlerRun.decCall_simple eps_u256_is_zero_ro ?_
      refine HandlerRun.dec_simple ?_
      refine HandlerRun.dec_simple ?_
      refine HandlerRun.seq_ite_unit
        (fun _ _ _ _ =>
          HandlerRun.seq_assoc
            (HandlerRun.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial)
              (HandlerRun.seq_assign_local (Q := fun _ => True) (fun _ _ _ _ _ => trivial) ?_)))
        (fun _ _ => HandlerRun.seq_skip ?_)
      all_goals
        refine HandlerRun.seq_call_simple eps_charge_gas_any ?_
        refine HandlerRun.seq_call_simple eps_charge_state_gas ?_
        refine HandlerRun.seq_call_assign_local_simple hW.eps_get_account ?_
        refine HandlerRun.dec_simple ?_
        refine HandlerRun.seq_call_simple hW.eps_move_ether ?_
        refine HandlerRun.decCall_simple eps_memeq_ro ?_
        refine HandlerRun.seq_ite_unit
          (fun _ _ _ _ => HandlerRun.seq_call_simple hW.eps_emit_transfer_log ?_)
          (fun _ _ => HandlerRun.seq_skip ?_)
        all_goals
          refine HandlerRun.decCall_simple eps_htab_has_ro ?_
          exact HandlerRun.seq_ite_unit
            (fun _ _ _ _ =>
              HandlerRun.seq_call (Q := fun _ => True) eps_htab_set_head_del
                (fun t _ _ _ _ hc hInv _ hargs hl => htab_set_head_del_callee_t t hInv hc hargs hl)
                (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
                (HandlerRun.seq_store_ev_nonstruct (Q := fun t => memW t (globN t "ev" + 104) = 0)
                  104 (by simp [nonStructFrameOffs])
                  (fun _ v _ hv => by
                    change some (ValueHOL.val (.word 0#64)) = some v at hv
                    injection hv with hv'; exact ⟨0, hv'.symm⟩)
                  (fun t w hw _ _ => by
                    change some (ValueHOL.val (.word 0#64)) = some (.val (.word w)) at hw
                    injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3; subst hw3
                    simpa [globN] using R14Shards.OpHandlersA.memW_updW_same t (globN t "ev" + 104) 0)
                  (HandlerRun.ret_done hRun (fun _ _ hP => Or.inr (Or.inl hP)) _)))
            (fun _ _ =>
              HandlerRun.seq_skip
                (HandlerRun.seq_store_ev_nonstruct (Q := fun t => memW t (globN t "ev" + 104) = 0)
                  104 (by simp [nonStructFrameOffs])
                  (fun _ v _ hv => by
                    change some (ValueHOL.val (.word 0#64)) = some v at hv
                    injection hv with hv'; exact ⟨0, hv'.symm⟩)
                  (fun t w hw _ _ => by
                    change some (ValueHOL.val (.word 0#64)) = some (.val (.word w)) at hw
                    injection hw with hw1; injection hw1 with hw2; injection hw2 with hw3; subst hw3
                    simpa [globN] using R14Shards.OpHandlersA.memW_updW_same t (globN t "ev" + 104) 0)
                  (HandlerRun.ret_done hRun (fun _ _ hP => Or.inr (Or.inl hP)) _)))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
