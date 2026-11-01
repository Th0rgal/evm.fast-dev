import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.DispatchWalk
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace InitECandidate.Solver.Wave8GuestInv.RunFramesRace
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

def GBodyOpDispatch : Prop :=
  (TerminatingFunBoundedOn GuestInv (ofString "op_add") K.«op_add») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_addmod") K.«op_addmod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_address") K.«op_address») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_and") K.«op_and») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_balance") K.«op_balance») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_basefee") K.«op_basefee») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blobbasefee") K.«op_blobbasefee») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blobhash") K.«op_blobhash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_blockhash") K.«op_blockhash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_byte") K.«op_byte») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_call") K.«op_call») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_callcode") K.«op_callcode») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldatacopy") K.«op_calldatacopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldataload") K.«op_calldataload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_calldatasize") K.«op_calldatasize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_caller") K.«op_caller») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_callvalue") K.«op_callvalue») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_chainid") K.«op_chainid») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_clz") K.«op_clz») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_codecopy") K.«op_codecopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_codesize") K.«op_codesize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_coinbase") K.«op_coinbase») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_create") K.«op_create») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_create2") K.«op_create2») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_delegatecall") K.«op_delegatecall») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_div") K.«op_div») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_dup") K.«op_dup») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_dupn") K.«op_dupn») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_eq") K.«op_eq») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_exchange") K.«op_exchange») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_exp") K.«op_exp») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodecopy") K.«op_extcodecopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodehash") K.«op_extcodehash») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_extcodesize") K.«op_extcodesize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gas") K.«op_gas») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gaslimit") K.«op_gaslimit») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gasprice") K.«op_gasprice») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_gt") K.«op_gt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_iszero") K.«op_iszero») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jump") K.«op_jump») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jumpdest") K.«op_jumpdest») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_jumpi") K.«op_jumpi») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_keccak") K.«op_keccak») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_log") K.«op_log») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_lt") K.«op_lt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mcopy") K.«op_mcopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mload") K.«op_mload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mod") K.«op_mod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_msize") K.«op_msize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mstore") K.«op_mstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mstore8") K.«op_mstore8») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mul") K.«op_mul») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_mulmod") K.«op_mulmod») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_not") K.«op_not») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_number") K.«op_number») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_or") K.«op_or») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_origin") K.«op_origin») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_pc") K.«op_pc») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_pop") K.«op_pop») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_prevrandao") K.«op_prevrandao») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_push") K.«op_push») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_return") K.«op_return») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_returndatacopy") K.«op_returndatacopy») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_returndatasize") K.«op_returndatasize») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_revert") K.«op_revert») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sar") K.«op_sar») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sdiv") K.«op_sdiv») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_selfbalance") K.«op_selfbalance») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_selfdestruct") K.«op_selfdestruct») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sgt") K.«op_sgt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_shl") K.«op_shl») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_shr") K.«op_shr») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_signextend") K.«op_signextend») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.«op_sload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_slotnum") K.«op_slotnum») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_slt") K.«op_slt») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_smod") K.«op_smod») →
  (TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.«op_sstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_staticcall") K.«op_staticcall») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_stop") K.«op_stop») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_sub") K.«op_sub») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_swap") K.«op_swap») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_swapn") K.«op_swapn») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_timestamp") K.«op_timestamp») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_tload") K.«op_tload») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_tstore") K.«op_tstore») →
  (TerminatingFunBoundedOn GuestInv (ofString "op_xor") K.«op_xor») →
  TerminatingFunBoundedOn EvmRun (ofString "op_dispatch") K.«op_dispatch»


theorem lookup_op_dispatch : originalRuntimeCode.lookup (ofString "op_dispatch") =
    some ((sourceFunctionEntry Guest.Software.guestFn_op_dispatch).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 577 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_op_dispatch) rfl

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
(DispatchWalk.ite _
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_stop _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_add _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_mul _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_sub _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_div _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_sdiv _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_mod _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_smod _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_addmod _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_mulmod _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_exp _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_signextend _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip))))))))))))
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_lt _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_gt _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_slt _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_sgt _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_eq _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_iszero _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_and _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_or _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_xor _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_not _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_byte _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_shl _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_shr _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_sar _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_clz _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip))))))))))))))))
(DispatchWalk.raise _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_keccak _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_address _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_balance _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_origin _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_caller _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_callvalue _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_calldataload _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_calldatasize _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_calldatacopy _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_codesize _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_codecopy _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_gasprice _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_extcodesize _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_extcodecopy _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_returndatasize _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_returndatacopy _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_extcodehash _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)))))))))))))))))
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_blockhash _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_coinbase _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_timestamp _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_number _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_prevrandao _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_gaslimit _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_chainid _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_selfbalance _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_basefee _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_blobhash _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_blobbasefee _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_slotnum _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_pop _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_mload _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_mstore _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_mstore8 _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_sload _ _ (dispatchEntry_run _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_sstore _ _ (dispatchEntry_run _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_jump _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_jumpi _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_pc _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_msize _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_gas _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_jumpdest _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_tload _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_tstore _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_mcopy _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_push _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)))))))))))))))))))))))))))))
(DispatchWalk.raise _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_push _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_dup _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.callReturn h_op_swap _ _ (dispatchEntry_guest _ _))))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_log _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_dupn _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_swapn _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_exchange _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_create _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_call _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_callcode _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_return _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_delegatecall _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_create2 _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_staticcall _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_revert _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.ite _
(DispatchWalk.callReturn h_op_selfdestruct _ _ (dispatchEntry_guest _ _))
DispatchWalk.skip)
(DispatchWalk.seq
(DispatchWalk.raise _ _)
(DispatchWalk.returned _)))))))))))))))))))
  · simp only [K.op_dispatch, Nat.add_assoc, Nat.add_zero]
    exact Nat.le_refl _

end InitECandidate.Solver.Wave8GuestInv.RunFramesRace
