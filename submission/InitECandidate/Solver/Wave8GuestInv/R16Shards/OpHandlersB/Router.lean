import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Router
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group06ControlFlow
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group07Transient
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group02
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers.Group03

/-! # OpDispatch Router Assembly (`op_dispatch_spec_of_remaining`)

Pre-`C00` router shard assembling `op_dispatch_spec_of_handlers` (`R11Shards/OpDispatchSpec/Router.lean`)
with all already-proved unconditional `OpHandlerSpec` leaves:
- Group 06a control-flow (`R16Shards.OpHandlersB.Group06ControlFlow`):
  `op_stop`, `op_jump`, `op_jumpi`, `op_pc`, `op_gas`, `op_jumpdest` (6)
- Group 07a transient storage (`R16Shards.OpHandlersB.Group07Transient`):
  `op_tload`, `op_tstore` (2)
- Group 02 comparisons (`R16Shards.OpHandlers.Group02`):
  `op_lt`, `op_gt`, `op_slt`, `op_sgt`, `op_eq`, `op_iszero` (6)
- Group 03 bitwise & shift (`R16Shards.OpHandlers.Group03`):
  `op_and`, `op_or`, `op_xor`, `op_not`, `op_byte`, `op_shl`, `op_shr`, `op_sar`, `op_clz` (9)

As each subsequent `OpHandlersB` group shard is completed, it is wired in here to monotonically
shrink the remaining obligation bundle for `op_dispatch_spec`.
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
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers

/-- Remaining `OpHandlerSpec` leaves in `OpHandlers-A` scope (Groups 01, 04, 05, 06b). -/
def RemainingOpHandlersASpec : Prop :=
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
  OpHandlerSpec (ofString "op_keccak") ∧
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
  OpHandlerSpec (ofString "op_mload") ∧
  OpHandlerSpec (ofString "op_mstore") ∧
  OpHandlerSpec (ofString "op_mstore8") ∧
  OpHandlerSpec (ofString "op_msize") ∧
  OpHandlerSpec (ofString "op_push") ∧
  OpHandlerSpec (ofString "op_dup") ∧
  OpHandlerSpec (ofString "op_swap") ∧
  OpHandlerSpec (ofString "op_dupn") ∧
  OpHandlerSpec (ofString "op_swapn") ∧
  OpHandlerSpec (ofString "op_exchange")

/-- Remaining `OpHandlerSpec` leaves in `OpHandlers-B` scope (Groups 07–10). -/
def RemainingOpHandlersBSpec : Prop :=
  OpHandlerSpec (ofString "op_balance") ∧
  OpHandlerSpec (ofString "op_calldatacopy") ∧
  OpHandlerSpec (ofString "op_codecopy") ∧
  OpHandlerSpec (ofString "op_extcodesize") ∧
  OpHandlerSpec (ofString "op_extcodecopy") ∧
  OpHandlerSpec (ofString "op_returndatacopy") ∧
  OpHandlerSpec (ofString "op_extcodehash") ∧
  OpHandlerSpec (ofString "op_selfbalance") ∧
  OpHandlerSpec (ofString "op_sload") ∧
  OpHandlerSpec (ofString "op_sstore") ∧
  OpHandlerSpec (ofString "op_mcopy") ∧
  OpHandlerSpec (ofString "op_log") ∧
  OpHandlerSpec (ofString "op_create") ∧
  OpHandlerSpec (ofString "op_call") ∧
  OpHandlerSpec (ofString "op_callcode") ∧
  OpHandlerSpec (ofString "op_return") ∧
  OpHandlerSpec (ofString "op_delegatecall") ∧
  OpHandlerSpec (ofString "op_create2") ∧
  OpHandlerSpec (ofString "op_staticcall") ∧
  OpHandlerSpec (ofString "op_revert") ∧
  OpHandlerSpec (ofString "op_selfdestruct")

theorem allOpHandlersSpec_of_remaining
    (hA : RemainingOpHandlersASpec)
    (hB : RemainingOpHandlersBSpec) :
    AllOpHandlersSpec := by
  rcases hA with
    ⟨h_op_add, h_op_mul, h_op_sub, h_op_div, h_op_sdiv, h_op_mod, h_op_smod,
     h_op_addmod, h_op_mulmod, h_op_exp, h_op_signextend,
     h_op_keccak, h_op_address, h_op_origin, h_op_caller, h_op_callvalue,
     h_op_calldataload, h_op_calldatasize, h_op_codesize, h_op_gasprice,
     h_op_returndatasize,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_msize,
     h_op_push, h_op_dup, h_op_swap, h_op_dupn, h_op_swapn, h_op_exchange⟩
  rcases hB with
    ⟨h_op_balance, h_op_calldatacopy, h_op_codecopy, h_op_extcodesize,
     h_op_extcodecopy, h_op_returndatacopy, h_op_extcodehash, h_op_selfbalance,
     h_op_sload, h_op_sstore, h_op_mcopy, h_op_log,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall, h_op_revert, h_op_selfdestruct⟩
  exact
    ⟨op_stop_spec, h_op_add, h_op_mul, h_op_sub, h_op_div, h_op_sdiv, h_op_mod, h_op_smod,
     h_op_addmod, h_op_mulmod, h_op_exp, h_op_signextend,
     op_lt_spec, op_gt_spec, op_slt_spec, op_sgt_spec, op_eq_spec, op_iszero_spec,
     op_and_spec, op_or_spec, op_xor_spec, op_not_spec, op_byte_spec, op_shl_spec, op_shr_spec, op_sar_spec, op_clz_spec,
     h_op_keccak, h_op_address, h_op_balance, h_op_origin, h_op_caller, h_op_callvalue,
     h_op_calldataload, h_op_calldatasize, h_op_calldatacopy,
     h_op_codesize, h_op_codecopy, h_op_gasprice, h_op_extcodesize, h_op_extcodecopy,
     h_op_returndatasize, h_op_returndatacopy, h_op_extcodehash,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_selfbalance, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_sload, h_op_sstore,
     op_jump_spec, op_jumpi_spec, op_pc_spec, h_op_msize, op_gas_spec, op_jumpdest_spec,
     op_tload_spec, op_tstore_spec, h_op_mcopy, h_op_push,
     h_op_dup, h_op_swap,
     h_op_log, h_op_dupn, h_op_swapn, h_op_exchange,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall,
     h_op_revert, h_op_selfdestruct⟩

/-- Parameterized `op_dispatch_spec` wired to all proved leaves in `Group06ControlFlow`, `Group07Transient`, `Group02`, and `Group03`. -/
theorem op_dispatch_spec_of
    (hA : RemainingOpHandlersASpec)
    (hB : RemainingOpHandlersBSpec) :
    OpHandlerSpec (ofString "op_dispatch") :=
  op_dispatch_spec_of_handlers (allOpHandlersSpec_of_remaining hA hB)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
