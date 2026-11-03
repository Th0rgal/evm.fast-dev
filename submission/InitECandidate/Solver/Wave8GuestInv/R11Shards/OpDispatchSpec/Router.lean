import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group01
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group02
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group03
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group04
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group05
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group06
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group07
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group08
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group09
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group10
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group11
import InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec.Group12

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def AllOpHandlersSpec : Prop :=
  OpHandlerSpec (ofString "op_stop") ∧
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
  OpHandlerSpec (ofString "op_lt") ∧
  OpHandlerSpec (ofString "op_gt") ∧
  OpHandlerSpec (ofString "op_slt") ∧
  OpHandlerSpec (ofString "op_sgt") ∧
  OpHandlerSpec (ofString "op_eq") ∧
  OpHandlerSpec (ofString "op_iszero") ∧
  OpHandlerSpec (ofString "op_and") ∧
  OpHandlerSpec (ofString "op_or") ∧
  OpHandlerSpec (ofString "op_xor") ∧
  OpHandlerSpec (ofString "op_not") ∧
  OpHandlerSpec (ofString "op_byte") ∧
  OpHandlerSpec (ofString "op_shl") ∧
  OpHandlerSpec (ofString "op_shr") ∧
  OpHandlerSpec (ofString "op_sar") ∧
  OpHandlerSpec (ofString "op_clz") ∧
  OpHandlerSpec (ofString "op_keccak") ∧
  OpHandlerSpec (ofString "op_address") ∧
  OpHandlerSpec (ofString "op_balance") ∧
  OpHandlerSpec (ofString "op_origin") ∧
  OpHandlerSpec (ofString "op_caller") ∧
  OpHandlerSpec (ofString "op_callvalue") ∧
  OpHandlerSpec (ofString "op_calldataload") ∧
  OpHandlerSpec (ofString "op_calldatasize") ∧
  OpHandlerSpec (ofString "op_calldatacopy") ∧
  OpHandlerSpec (ofString "op_codesize") ∧
  OpHandlerSpec (ofString "op_codecopy") ∧
  OpHandlerSpec (ofString "op_gasprice") ∧
  OpHandlerSpec (ofString "op_extcodesize") ∧
  OpHandlerSpec (ofString "op_extcodecopy") ∧
  OpHandlerSpec (ofString "op_returndatasize") ∧
  OpHandlerSpec (ofString "op_returndatacopy") ∧
  OpHandlerSpec (ofString "op_extcodehash") ∧
  OpHandlerSpec (ofString "op_blockhash") ∧
  OpHandlerSpec (ofString "op_coinbase") ∧
  OpHandlerSpec (ofString "op_timestamp") ∧
  OpHandlerSpec (ofString "op_number") ∧
  OpHandlerSpec (ofString "op_prevrandao") ∧
  OpHandlerSpec (ofString "op_gaslimit") ∧
  OpHandlerSpec (ofString "op_chainid") ∧
  OpHandlerSpec (ofString "op_selfbalance") ∧
  OpHandlerSpec (ofString "op_basefee") ∧
  OpHandlerSpec (ofString "op_blobhash") ∧
  OpHandlerSpec (ofString "op_blobbasefee") ∧
  OpHandlerSpec (ofString "op_slotnum") ∧
  OpHandlerSpec (ofString "op_pop") ∧
  OpHandlerSpec (ofString "op_mload") ∧
  OpHandlerSpec (ofString "op_mstore") ∧
  OpHandlerSpec (ofString "op_mstore8") ∧
  OpHandlerSpec (ofString "op_sload") ∧
  OpHandlerSpec (ofString "op_sstore") ∧
  OpHandlerSpec (ofString "op_jump") ∧
  OpHandlerSpec (ofString "op_jumpi") ∧
  OpHandlerSpec (ofString "op_pc") ∧
  OpHandlerSpec (ofString "op_msize") ∧
  OpHandlerSpec (ofString "op_gas") ∧
  OpHandlerSpec (ofString "op_jumpdest") ∧
  OpHandlerSpec (ofString "op_tload") ∧
  OpHandlerSpec (ofString "op_tstore") ∧
  OpHandlerSpec (ofString "op_mcopy") ∧
  OpHandlerSpec (ofString "op_push") ∧
  OpHandlerSpec (ofString "op_dup") ∧
  OpHandlerSpec (ofString "op_swap") ∧
  OpHandlerSpec (ofString "op_log") ∧
  OpHandlerSpec (ofString "op_dupn") ∧
  OpHandlerSpec (ofString "op_swapn") ∧
  OpHandlerSpec (ofString "op_exchange") ∧
  OpHandlerSpec (ofString "op_create") ∧
  OpHandlerSpec (ofString "op_call") ∧
  OpHandlerSpec (ofString "op_callcode") ∧
  OpHandlerSpec (ofString "op_return") ∧
  OpHandlerSpec (ofString "op_delegatecall") ∧
  OpHandlerSpec (ofString "op_create2") ∧
  OpHandlerSpec (ofString "op_staticcall") ∧
  OpHandlerSpec (ofString "op_revert") ∧
  OpHandlerSpec (ofString "op_selfdestruct")

theorem dispatchCode_walk (h : AllOpHandlersSpec) :
    DispatchSpecWalk dispatchCode := by
  rcases h with
    ⟨h_op_stop, h_op_add, h_op_mul, h_op_sub, h_op_div, h_op_sdiv, h_op_mod, h_op_smod,
     h_op_addmod, h_op_mulmod, h_op_exp, h_op_signextend,
     h_op_lt, h_op_gt, h_op_slt, h_op_sgt, h_op_eq, h_op_iszero,
     h_op_and, h_op_or, h_op_xor, h_op_not, h_op_byte, h_op_shl, h_op_shr, h_op_sar, h_op_clz,
     h_op_keccak, h_op_address, h_op_balance, h_op_origin, h_op_caller, h_op_callvalue,
     h_op_calldataload, h_op_calldatasize, h_op_calldatacopy,
     h_op_codesize, h_op_codecopy, h_op_gasprice, h_op_extcodesize, h_op_extcodecopy,
     h_op_returndatasize, h_op_returndatacopy, h_op_extcodehash,
     h_op_blockhash, h_op_coinbase, h_op_timestamp, h_op_number, h_op_prevrandao,
     h_op_gaslimit, h_op_chainid, h_op_selfbalance, h_op_basefee, h_op_blobhash,
     h_op_blobbasefee, h_op_slotnum,
     h_op_pop, h_op_mload, h_op_mstore, h_op_mstore8, h_op_sload, h_op_sstore,
     h_op_jump, h_op_jumpi, h_op_pc, h_op_msize, h_op_gas, h_op_jumpdest,
     h_op_tload, h_op_tstore, h_op_mcopy, h_op_push,
     h_op_dup, h_op_swap,
     h_op_log, h_op_dupn, h_op_swapn, h_op_exchange,
     h_op_create, h_op_call, h_op_callcode, h_op_return, h_op_delegatecall,
     h_op_create2, h_op_staticcall,
     h_op_revert, h_op_selfdestruct⟩
  exact
    DispatchSpecWalk.seq
      (DispatchSpecWalk.ite _
        (DispatchSpecWalk.seq
          (DispatchSpecWalk.ite _
            (opDispatchSpecGroup01 h_op_stop h_op_add h_op_mul h_op_sub h_op_div h_op_sdiv
              h_op_mod h_op_smod h_op_addmod h_op_mulmod h_op_exp h_op_signextend)
            (opDispatchSpecGroup02 h_op_lt h_op_gt h_op_slt h_op_sgt h_op_eq h_op_iszero
              (opDispatchSpecGroup03 h_op_and h_op_or h_op_xor h_op_not h_op_byte h_op_shl
                h_op_shr h_op_sar h_op_clz)))
          (DispatchSpecWalk.raise _))
        DispatchSpecWalk.skip)
      (DispatchSpecWalk.seq
        (DispatchSpecWalk.ite _
          (DispatchSpecWalk.seq
            (DispatchSpecWalk.ite _
              (opDispatchSpecGroup04 h_op_keccak h_op_address h_op_balance h_op_origin
                h_op_caller h_op_callvalue h_op_calldataload h_op_calldatasize h_op_calldatacopy
                (opDispatchSpecGroup05 h_op_codesize h_op_codecopy h_op_gasprice h_op_extcodesize
                  h_op_extcodecopy h_op_returndatasize h_op_returndatacopy h_op_extcodehash))
              (opDispatchSpecGroup06 h_op_blockhash h_op_coinbase h_op_timestamp h_op_number
                h_op_prevrandao h_op_gaslimit h_op_chainid h_op_selfbalance h_op_basefee
                h_op_blobhash h_op_blobbasefee h_op_slotnum
                (opDispatchSpecGroup07 h_op_pop h_op_mload h_op_mstore h_op_mstore8
                  h_op_sload h_op_sstore
                  (opDispatchSpecGroup08 h_op_jump h_op_jumpi h_op_pc h_op_msize h_op_gas
                    h_op_jumpdest h_op_tload h_op_tstore h_op_mcopy h_op_push))))
            (DispatchSpecWalk.raise _))
          DispatchSpecWalk.skip)
        (opDispatchSpecGroup09 h_op_push h_op_dup h_op_swap
          (opDispatchSpecGroup10 h_op_log h_op_dupn h_op_swapn h_op_exchange
            (opDispatchSpecGroup11 h_op_create h_op_call h_op_callcode h_op_return
              h_op_delegatecall h_op_create2 h_op_staticcall
              (opDispatchSpecGroup12 h_op_revert h_op_selfdestruct)))))

theorem op_dispatch_spec_of_handlers (h : AllOpHandlersSpec) :
    OpHandlerSpec (ofString "op_dispatch") := by
  refine ⟨_, _, _, lookup_op_dispatch, ?_⟩
  intro F s hcode hRun _ hnt
  change OpDispatchPost s (evaluateHOLFiniteState s dispatchCode).1 (evaluateHOLFiniteState s dispatchCode).2
  rcases hres : evaluateHOLFiniteState s dispatchCode with ⟨r, post⟩
  cases r with
  | none =>
    exact opDispatchPost_other (by intro _ hv; cases hv) (by rintro ⟨_, hv⟩; cases hv)
  | some r0 =>
    have hwalk := (dispatchCode_walk h).run s hcode hRun hnt
    rw [hres] at hwalk
    exact hwalk.2 (by simp)

end InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
