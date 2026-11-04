import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.UntypedBufHelpers
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.JournalTransientHelpers

/-! # OpHandlerSpec Group 07a: transient storage opcodes (`op_tload`, `op_tstore`) -/

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

theorem u256_to_be32_callee_out_eq_key {F : Type}
    (t : PanSemStateFiniteExact 64 F)
    {kvVar : MlS}
    {values : List (ValueHOL 64)} {body' : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {ret' : ShapeHOL}
    (hc : t.code = originalRuntimeCode)
    (hkey : locN t "key" = globN t "evm_key_buf")
    (hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a))
      [.var .local kvVar, .var .local (ofString "key")] = some values)
    (hl : lookupCodeHOLFinite t.code.lookup (ofString "u256_to_be32") values =
      some (body', callee, ret')) :
    locN (callEntryStateHOLFinite t callee) "out" =
      globN (callEntryStateHOLFinite t callee) "evm_key_buf" := by
  rw [evalListHOLFinite_eq_toExact] at hargs
  unfold evalListHOLExact at hargs
  rcases hkv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.var .local kvVar) with _ | vkv
  · rw [hkv] at hargs; simp at hargs
  · rw [hkv] at hargs
    unfold evalListHOLExact at hargs
    rcases hk : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
        (.var .local (ofString "key")) with _ | vkey
    · rw [hk] at hargs; simp at hargs
    · rw [hk] at hargs
      unfold evalListHOLExact at hargs
      dsimp only at hargs
      injection hargs with hv_eq
      subst hv_eq
      have hx := PanSemStateFiniteExact.lookupCodeHOLFinite_eq_some
        t.code.lookup (ofString "u256_to_be32") [vkv, vkey] body' callee ret' hl
      rw [hc] at hx
      simp only [Flapjack.lookupCodeHOLExact, lookup_u256_to_be32_b] at hx
      split at hx
      · have hmap := congrArg (fun x => x.2.1) (Option.some.inj hx)
        have hcal_out : callee.lookup (ofString "out") = some vkey := by
          have := congrFun hmap.symm (ofString "out")
          simpa [List.map, List.zip, List.foldl] using this
        have ht_key : t.locals.lookup (ofString "key") = some vkey := by
          simpa [evalHOLExact] using hk
        have hloc_eq : locN (callEntryStateHOLFinite t callee) "out" = locN t "key" := by
          simp [callEntryStateHOLFinite, locN, hcal_out, ht_key]
        exact hloc_eq.trans hkey
      · cases hx

theorem dec_key_evm_key_buf_eq {F : Type}
    (t : PanSemStateFiniteExact 64 F) (v : ValueHOL 64)
    (hv : @evalHOLExact 64 F _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.var .global (ofString "evm_key_buf")) = some v) :
    locN (setVarHOLFinite (ofString "key") v t) "key" =
      globN (setVarHOLFinite (ofString "key") v t) "evm_key_buf" := by
  have hg : t.globals.lookup (ofString "evm_key_buf") = some v := by
    simpa [evalHOLExact] using hv
  simp [setVarHOLFinite, locN, globN, HolFiniteMapExact.lookup_update, FUPDATE, hg]

theorem op_tload_spec : OpHandlerSpec (ofString "op_tload") := by
  refine opHandlerSpec_of_run 529 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_tload rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_tload, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.decCall_simple eps_stack_pop
      (HandlerRun.seq_charge_gas_const (by decide)
        (HandlerRun.dec (Q := fun t => locN t "key" = globN t "evm_key_buf")
          (fun t v hv _ _ => dec_key_evm_key_buf_eq t v hv)
          (HandlerRun.seq_call (Q := fun _ => True)
            eps_u256_to_be32_evm_key_buf
            (fun t _ _ _ _ hc _ hP hargs hl =>
              u256_to_be32_callee_out_eq_key t hc hP hargs hl)
            (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
            (HandlerRun.dec_simple
              (HandlerRun.decCall_simple eps_get_transient_storage
                (HandlerRun.seq_call_simple eps_stack_push
                  (HandlerRun.seq_call_simple eps_pc_add
                    (HandlerRun.ret _))))))))

theorem op_tstore_spec : OpHandlerSpec (ofString "op_tstore") := by
  refine opHandlerSpec_of_run 530 (by rw [guestAst_len]; decide) Guest.Software.guestFn_op_tstore rfl ?_
  intro F s0 _
  dsimp only [Guest.Software.guestFn_op_tstore, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural]
  exact
    HandlerRun.seq_call_simple eps_require_not_static
      (HandlerRun.decCall_simple eps_stack_pop
        (HandlerRun.decCall_simple eps_stack_pop
          (HandlerRun.seq_charge_gas_const (by decide)
            (HandlerRun.dec (Q := fun t => locN t "key" = globN t "evm_key_buf")
              (fun t v hv _ _ => dec_key_evm_key_buf_eq t v hv)
              (HandlerRun.seq_call (Q := fun _ => True)
                eps_u256_to_be32_evm_key_buf
                (fun t _ _ _ _ hc _ hP hargs hl =>
                  u256_to_be32_callee_out_eq_key t hc hP hargs hl)
                (fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ => trivial)
                (HandlerRun.dec_simple
                  (HandlerRun.seq_call_simple eps_set_transient_storage
                    (HandlerRun.seq_call_simple eps_pc_add
                      (HandlerRun.ret _)))))))))

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
