import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup01
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup02
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup03
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup04
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup05
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup06
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup07
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup08
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup09
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup10
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup11
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.OpDispatchGroup12
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.GuardedBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.RunFramesRace
theorem gbody_op_dispatch : GBodyOpDispatch := by
  intro h_op_add h_op_addmod h_op_address h_op_and h_op_balance h_op_basefee h_op_blobbasefee h_op_blobhash h_op_blockhash h_op_byte h_op_call h_op_callcode h_op_calldatacopy h_op_calldataload h_op_calldatasize h_op_caller h_op_callvalue h_op_chainid h_op_clz h_op_codecopy h_op_codesize h_op_coinbase h_op_create h_op_create2 h_op_delegatecall h_op_div h_op_dup h_op_dupn h_op_eq h_op_exchange h_op_exp h_op_extcodecopy h_op_extcodehash h_op_extcodesize h_op_gas h_op_gaslimit h_op_gasprice h_op_gt h_op_iszero h_op_jump h_op_jumpdest h_op_jumpi h_op_keccak h_op_log h_op_lt h_op_mcopy h_op_mload h_op_mod h_op_msize h_op_mstore h_op_mstore8 h_op_mul h_op_mulmod h_op_not h_op_number h_op_or h_op_origin h_op_pc h_op_pop h_op_prevrandao h_op_push h_op_return h_op_returndatacopy h_op_returndatasize h_op_revert h_op_sar h_op_sdiv h_op_selfbalance h_op_selfdestruct h_op_sgt h_op_shl h_op_shr h_op_signextend h_op_sload h_op_slotnum h_op_slt h_op_smod h_op_sstore h_op_staticcall h_op_stop h_op_sub h_op_swap h_op_swapn h_op_timestamp h_op_tload h_op_tstore h_op_xor
  refine ⟨_, _, _, lookup_op_dispatch, ?_⟩
  simp only [sourceFunctionEntry, Guest.Software.guestFn_op_dispatch,
    InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.funDeclToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map_none, Option.map_some, List.map_cons, List.map_nil]
  apply TerminatingProgBoundedOn.mono_bound
  · exact DispatchWalk.bound (
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.seq
(DispatchWalk.ite
_
(opDispatchGroup01 h_op_stop h_op_add h_op_mul h_op_sub h_op_div h_op_sdiv h_op_mod h_op_smod h_op_addmod h_op_mulmod h_op_exp h_op_signextend)
(opDispatchGroup02 h_op_lt h_op_gt h_op_slt h_op_sgt h_op_eq h_op_iszero
(opDispatchGroup03 h_op_and h_op_or h_op_xor h_op_not h_op_byte h_op_shl h_op_shr h_op_sar h_op_clz)))
(DispatchWalk.raise
_
_))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite
_
(DispatchWalk.seq
(DispatchWalk.ite
_
(opDispatchGroup04 h_op_keccak h_op_address h_op_balance h_op_origin h_op_caller h_op_callvalue h_op_calldataload h_op_calldatasize h_op_calldatacopy
(opDispatchGroup05 h_op_codesize h_op_codecopy h_op_gasprice h_op_extcodesize h_op_extcodecopy h_op_returndatasize h_op_returndatacopy h_op_extcodehash))
(opDispatchGroup06 h_op_blockhash h_op_coinbase h_op_timestamp h_op_number h_op_prevrandao h_op_gaslimit h_op_chainid h_op_selfbalance h_op_basefee h_op_blobhash h_op_blobbasefee h_op_slotnum
(opDispatchGroup07 h_op_pop h_op_mload h_op_mstore h_op_mstore8 h_op_sload h_op_sstore
(opDispatchGroup08 h_op_jump h_op_jumpi h_op_pc h_op_msize h_op_gas h_op_jumpdest h_op_tload h_op_tstore h_op_mcopy h_op_push))))
(DispatchWalk.raise
_
_))
DispatchWalk.skip)
(opDispatchGroup09 h_op_push h_op_dup h_op_swap
(opDispatchGroup10 h_op_log h_op_dupn h_op_swapn h_op_exchange
(opDispatchGroup11 h_op_create h_op_call h_op_callcode h_op_return h_op_delegatecall h_op_create2 h_op_staticcall
(opDispatchGroup12 h_op_revert h_op_selfdestruct)))))))
  · simp only [K.op_dispatch, dispatchCost01, dispatchCost02, dispatchCost03, dispatchCost04, dispatchCost05, dispatchCost06, dispatchCost07, dispatchCost08, dispatchCost09, dispatchCost10, dispatchCost11, dispatchCost12, Nat.add_assoc, Nat.add_zero]
    exact Nat.le_refl _


end InitECandidate.Solver.Wave8GuestInv.GuardedBody
