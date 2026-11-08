import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.Common
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.ReadOnly
import InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA.StackPush
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.CalldataloadSpecs
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group01
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group04
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group05bEnv
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group06Stack2
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group06Stack3

/-! # OpHandlerSpec Group 06 (`OpHandlers-A`): remaining `OpHandlers-A` assembly -/

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

def RemainingOpHandlersASpecAligned : Prop :=
  OpHandlerSpec (ofString "op_add") ∧
  OpHandlerSpec (ofString "op_mul") ∧
  OpHandlerSpec (ofString "op_sub") ∧
  OpHandlerSpec (ofString "op_div") ∧
  OpHandlerSpec (ofString "op_sdiv") ∧
  OpHandlerSpec (ofString "op_mod") ∧
  OpHandlerSpec (ofString "op_smod") ∧
  OpHandlerSpec (ofString "op_addmod") ∧
  OpHandlerSpec (ofString "op_mulmod") ∧
  OpHandlerSpec (ofString "op_exp") ∧
  OpHandlerSpec (ofString "op_signextend") ∧
  FunSpec (fun s => EvmRun s ∧ HeadMemAligned s) OpDispatchPost (ofString "op_keccak") ∧
  OpHandlerSpec (ofString "op_address") ∧
  OpHandlerSpec (ofString "op_origin") ∧
  OpHandlerSpec (ofString "op_caller") ∧
  OpHandlerSpec (ofString "op_callvalue") ∧
  OpHandlerSpec (ofString "op_calldataload") ∧
  OpHandlerSpec (ofString "op_calldatasize") ∧
  OpHandlerSpec (ofString "op_codesize") ∧
  OpHandlerSpec (ofString "op_gasprice") ∧
  OpHandlerSpec (ofString "op_returndatasize") ∧
  OpHandlerSpec (ofString "op_blockhash") ∧
  OpHandlerSpec (ofString "op_coinbase") ∧
  OpHandlerSpec (ofString "op_timestamp") ∧
  OpHandlerSpec (ofString "op_number") ∧
  OpHandlerSpec (ofString "op_prevrandao") ∧
  OpHandlerSpec (ofString "op_gaslimit") ∧
  OpHandlerSpec (ofString "op_chainid") ∧
  OpHandlerSpec (ofString "op_basefee") ∧
  OpHandlerSpec (ofString "op_blobhash") ∧
  OpHandlerSpec (ofString "op_blobbasefee") ∧
  OpHandlerSpec (ofString "op_slotnum") ∧
  OpHandlerSpec (ofString "op_pop") ∧
  OpHandlerSpec (ofString "op_msize") ∧
  FunSpec
    (fun s => EvmRun s ∧
      ∃ n : BitVec 64, s.locals.lookup (ofString "nbytes") = some (.val (.word n)) ∧ n.toNat ≤ 32)
    OpDispatchPost
    (ofString "op_push") ∧
  OpHandlerSpec (ofString "op_dup") ∧
  OpHandlerSpec (ofString "op_swap") ∧
  OpHandlerSpec (ofString "op_dupn") ∧
  OpHandlerSpec (ofString "op_swapn") ∧
  OpHandlerSpec (ofString "op_exchange")

theorem remainingOpHandlersASpecAligned_proved : RemainingOpHandlersASpecAligned :=
  ⟨op_add_spec, op_mul_spec, op_sub_spec, op_div_spec, op_sdiv_spec, op_mod_spec, op_smod_spec,
   op_addmod_spec, op_mulmod_spec, op_exp_spec, op_signextend_spec, op_keccak_aligned_spec,
   op_address_spec, op_origin_spec, op_caller_spec, op_callvalue_spec, op_calldataload_spec,
   op_calldatasize_spec, op_codesize_spec, op_gasprice_spec, op_returndatasize_spec,
   op_blockhash_spec, op_coinbase_spec, op_timestamp_spec, op_number_spec, op_prevrandao_spec,
   op_gaslimit_spec, op_chainid_spec, op_basefee_spec, op_blobhash_spec, op_blobbasefee_spec,
   op_slotnum_spec, op_pop_spec, op_msize_spec, op_push_bounded_spec, op_dup_spec, op_swap_spec,
   op_dupn_spec, op_swapn_spec, op_exchange_spec⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
