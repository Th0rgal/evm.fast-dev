import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
import InitECandidate.Solver.Wave8GuestInv.GuardedBody.PtxPhase1BackingCut
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.Depth0FrameOpenTail
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10ChildBridge
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.OpLogBridgeR29
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyPayloadHeaderExport
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockAuxLeaves
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBlockRlpLength
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkBuildMptIndexedRoot
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDecodeHostInputMain
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkEncodeTxBounded
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPmcMarksBo
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase1
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxRelBasePhase3
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkRequestsAppend

/-! # Wave 8 R29 Cutover Strong Bridges (`StrongBridgesR29`)

Zero-`sorry` companion to `ContractParts/StrongBridges.lean` keeping each shard well under
1,500 lines and leaving `StrongBridges.lean`, `PrimitivesProved.lean`, `Assembly.lean`,
`Target.lean`, and `Certificate.lean` untouched (preserving `Wave8Stage.StageTransfer`
binary `.olean` compatibility).

Key R29 integrations:
1. **Bounded `op_log` (`ntopics ≤ 4`)**: exports `op_log_bounded_aligned_spec` and
   `op_log_bounded_chain_spec` from `OpLogBridgeR29`, discharging `op_log` in both
   `OpDispatchAlignedSpec` (closing 81/87 aligned handlers, leaving only the 6 call/create
   opcodes) and `OpDispatchChainHandlersCutover`.
2. **All 7 Group 10 call/create chain-WF opcodes (`Group10ChildBridge`)**: lifts
   `group10_child_bridge_g10` (`op_create`, `op_call`, `op_callcode`, `op_delegatecall`,
   `op_create2`, `op_staticcall`, `op_selfdestruct`) into `HeadMemBridge.HeadMemChainWF`
   via `opHandlerChainSpecA_of_g10`, discharging `op_call`, `op_callcode`, `op_staticcall`,
   and `op_log` from `StrongBridges.RemainingChainHandlersCutover` so all 11 Group 09/10/log/mcopy
   chain-WF opcodes are closed into `OpDispatchSpecA` and `gbody_run_frames_aligned`.
3. **GuardedBody Phase 1 backing cut (`PtxPhase1BackingCut`)**: closes `PtxPhase1BackingCut`
   from `ptxPhase1_backing_cut` + `PtxPhase2BackingCut` into `gbody_process_transaction`
   on `TxReadyBackingStrong`.
4. **Relational `process_transaction` strong cuts (`WkPtxPhase1`, `WkPtxRelBasePhase3`,
   `WkPmcMarksBo`, `PtxPhase2StrongTail5`)**: composes `ptxPhase1_relCut_strong` (on
   `PtxEntryFull` via `txReadyFullStrong_init`), `ptxPhase2_cut_strong`,
   `ptxPhase3_relCut_strong (wk_process_message_call_marks_bo_of_callees hpm hpcm)`, and
   Phase 5 (`decode_witness_to_mpt_spec_wkBal`) into `wk_process_transaction` on
   `TxReadyFullStrong` (and `TxReadyStrong`).
5. **TopGbodyWk, BlockAux, MptRoot, and SetCode R29 exports**: surfaces zero-`sorry`
   `gbody_payload_header`, `wk_block_rlp_length`, `wk_decode_host_input_strong_sound`,
   `wk_decode_host_input_of_nonempty`, `wk_encode_transaction_bounded`,
   `wk_check_transaction_bo`, `wk_recover_sender_with_chain_id_bo`, `wk_requests_append`,
   `wkSc_idx_start_storage_of_witnessDb`, `wkSc_update_builder_from_tx_of_witnessDb`,
   `wkSc_process_withdrawals_of_witnessDb`, `wk_process_withdrawals_of_witnessDb`,
   `wk_process_unchecked_system_transaction_of_witnessDb`,
   `wk_process_checked_system_transaction_of_witnessDb`, `eval_call_mpt_root_fresh`, and
   `funSpec_set_code_msgBounded` / `fk_set_code_msgBounded` / `hoare_d0PreB_call_set_code`.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges

/-! ## 1. Bounded `op_log` Aligned Router Closure (81/87 Handlers Closed) -/

theorem op_log_bounded_aligned_spec :
    R16Shards.OpHandlersB.OpLogBoundedAlignedSpec :=
  R16Shards.OpHandlersB.op_log_bounded_aligned_spec

theorem op_log_bounded_chain_spec :
    R16Shards.OpHandlersB.OpLogBoundedChainSpec :=
  R16Shards.OpHandlersB.op_log_bounded_chain_spec

/-- The 6 remaining aligned call/create handler obligations once `op_log` (`ntopics ≤ 4`)
is discharged by `OpLogBridgeR29.op_log_bounded_aligned_spec`. -/
structure RemainingCallCreateAlignedSpecsR29 : Prop where
  op_create : R16Shards.OpHandlersB.RouterAligned.OpHandlerSpecA (ofString "op_create")
  op_call : R16Shards.OpHandlersB.RouterAligned.OpHandlerSpecA (ofString "op_call")
  op_callcode : R16Shards.OpHandlersB.RouterAligned.OpHandlerSpecA (ofString "op_callcode")
  op_delegatecall : R16Shards.OpHandlersB.RouterAligned.OpHandlerSpecA (ofString "op_delegatecall")
  op_create2 : R16Shards.OpHandlersB.RouterAligned.OpHandlerSpecA (ofString "op_create2")
  op_staticcall : R16Shards.OpHandlersB.RouterAligned.OpHandlerSpecA (ofString "op_staticcall")

theorem remainingCallCreateLogAlignedSpecs_of_r29
    (h : RemainingCallCreateAlignedSpecsR29) :
    R16Shards.OpHandlersB.RemainingCallCreateLogAlignedSpecs where
  op_log := op_log_bounded_aligned_spec
  op_create := h.op_create
  op_call := h.op_call
  op_callcode := h.op_callcode
  op_delegatecall := h.op_delegatecall
  op_create2 := h.op_create2
  op_staticcall := h.op_staticcall

/-- Aligned `op_dispatch` router with `ExtCodeOfHeadSpec` and bounded `op_log` closed
(81 of 87 handlers closed under `WorldAccountSpecs`). -/
theorem op_dispatch_aligned_spec_r29
    (hW : R16Shards.OpHandlersB.WorldAccountSpecs)
    (hrem : RemainingCallCreateAlignedSpecsR29) :
    R16Shards.OpHandlersB.RouterAligned.OpDispatchAlignedSpec :=
  op_dispatch_aligned_spec_cutover_closed hW
    (remainingCallCreateLogAlignedSpecs_of_r29 hrem)

/-! ## 2. Group 10 Call/Create + `op_log` Chain-WF Router Closure -/

theorem group10_child_bridge_g10 :
    type_of% @R16Shards.OpHandlersB.group10_child_bridge_g10 :=
  R16Shards.OpHandlersB.group10_child_bridge_g10

theorem op_call_chainSpecA
    (hWc : R16Shards.OpHandlersB.WorldAccountSpecsCall_g10)
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerChainSpecA (ofString "op_call") :=
  opHandlerChainSpecA_of_g10 (R16Shards.OpHandlersB.op_call_specA_g10 hWc hgca)

theorem op_callcode_chainSpecA
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerChainSpecA (ofString "op_callcode") :=
  opHandlerChainSpecA_of_g10 (R16Shards.OpHandlersB.op_callcode_specA_g10 hW hgca)

theorem op_staticcall_chainSpecA
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call")) :
    OpHandlerChainSpecA (ofString "op_staticcall") :=
  opHandlerChainSpecA_of_g10 (R16Shards.OpHandlersB.op_staticcall_specA_g10 hW hgca)

/-- All 7 Group 10 call/create opcodes lifted to `HeadMemBridge.HeadMemChainWF` via
`Group10ChildBridge.group10_child_bridge_g10`. -/
theorem group10_chainSpecsA_of_child_bridge
    (hWc : R16Shards.OpHandlersB.WorldAccountSpecsCall_g10)
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgcr : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create"))
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32")) :
    OpHandlerChainSpecA (ofString "op_create") ∧
    OpHandlerChainSpecA (ofString "op_call") ∧
    OpHandlerChainSpecA (ofString "op_callcode") ∧
    OpHandlerChainSpecA (ofString "op_delegatecall") ∧
    OpHandlerChainSpecA (ofString "op_create2") ∧
    OpHandlerChainSpecA (ofString "op_staticcall") ∧
    OpHandlerChainSpecA (ofString "op_selfdestruct") := by
  obtain ⟨hc, hcl, hccode, hdc, hc2, hsc, hsd⟩ :=
    R16Shards.OpHandlersB.group10_child_bridge_g10 hWc hcc hcc2 hgcr hgca hU
  exact ⟨opHandlerChainSpecA_of_g10 hc,
    opHandlerChainSpecA_of_g10 hcl,
    opHandlerChainSpecA_of_g10 hccode,
    opHandlerChainSpecA_of_g10 hdc,
    opHandlerChainSpecA_of_g10 hc2,
    opHandlerChainSpecA_of_g10 hsc,
    opHandlerChainSpecA_of_g10 hsd⟩

/-- Remaining chain-WF A-side/memory handler obligations after R29 closes all 11 Group 09/10,
`op_mcopy`, and bounded `op_log` (`ntopics ≤ 4`) chain-WF opcodes. -/
structure RemainingChainHandlersR29 : Prop where
  op_stop : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_stop")
  op_add : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_add")
  op_mul : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mul")
  op_sub : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sub")
  op_div : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_div")
  op_sdiv : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sdiv")
  op_mod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mod")
  op_smod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_smod")
  op_addmod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_addmod")
  op_mulmod : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mulmod")
  op_exp : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_exp")
  op_signextend : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_signextend")
  op_lt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_lt")
  op_gt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gt")
  op_slt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_slt")
  op_sgt : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sgt")
  op_eq : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_eq")
  op_iszero : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_iszero")
  op_and : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_and")
  op_or : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_or")
  op_xor : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_xor")
  op_not : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_not")
  op_byte : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_byte")
  op_shl : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_shl")
  op_shr : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_shr")
  op_sar : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sar")
  op_clz : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_clz")
  op_keccak : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_keccak")
  op_address : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_address")
  op_balance : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_balance")
  op_origin : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_origin")
  op_caller : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_caller")
  op_callvalue : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_callvalue")
  op_calldataload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_calldataload")
  op_calldatasize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_calldatasize")
  op_calldatacopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_calldatacopy")
  op_codesize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_codesize")
  op_codecopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_codecopy")
  op_gasprice : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gasprice")
  op_extcodesize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_extcodesize")
  op_extcodecopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_extcodecopy")
  op_returndatasize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_returndatasize")
  op_returndatacopy : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_returndatacopy")
  op_extcodehash : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_extcodehash")
  op_blockhash : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_blockhash")
  op_coinbase : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_coinbase")
  op_timestamp : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_timestamp")
  op_number : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_number")
  op_prevrandao : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_prevrandao")
  op_gaslimit : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gaslimit")
  op_chainid : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_chainid")
  op_selfbalance : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_selfbalance")
  op_basefee : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_basefee")
  op_blobhash : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_blobhash")
  op_blobbasefee : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_blobbasefee")
  op_slotnum : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_slotnum")
  op_pop : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_pop")
  op_mload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mload")
  op_mstore : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mstore")
  op_mstore8 : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_mstore8")
  op_sload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sload")
  op_sstore : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_sstore")
  op_jump : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_jump")
  op_jumpi : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_jumpi")
  op_pc : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_pc")
  op_msize : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_msize")
  op_gas : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_gas")
  op_jumpdest : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_jumpdest")
  op_tload : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_tload")
  op_tstore : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_tstore")
  op_push : R16Shards.OpHandlersB.OpPushBoundedChainSpec
  op_dup : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_dup")
  op_swap : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_swap")
  op_dupn : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_dupn")
  op_swapn : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_swapn")
  op_exchange : R16Shards.OpHandlersB.OpHandlerChainSpec (ofString "op_exchange")

theorem remainingChainHandlersCutover_of_r29
    (hWc : R16Shards.OpHandlersB.WorldAccountSpecsCall_g10)
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hrem : RemainingChainHandlersR29) :
    RemainingChainHandlersCutover where
  op_stop := hrem.op_stop
  op_add := hrem.op_add
  op_mul := hrem.op_mul
  op_sub := hrem.op_sub
  op_div := hrem.op_div
  op_sdiv := hrem.op_sdiv
  op_mod := hrem.op_mod
  op_smod := hrem.op_smod
  op_addmod := hrem.op_addmod
  op_mulmod := hrem.op_mulmod
  op_exp := hrem.op_exp
  op_signextend := hrem.op_signextend
  op_lt := hrem.op_lt
  op_gt := hrem.op_gt
  op_slt := hrem.op_slt
  op_sgt := hrem.op_sgt
  op_eq := hrem.op_eq
  op_iszero := hrem.op_iszero
  op_and := hrem.op_and
  op_or := hrem.op_or
  op_xor := hrem.op_xor
  op_not := hrem.op_not
  op_byte := hrem.op_byte
  op_shl := hrem.op_shl
  op_shr := hrem.op_shr
  op_sar := hrem.op_sar
  op_clz := hrem.op_clz
  op_keccak := hrem.op_keccak
  op_address := hrem.op_address
  op_balance := hrem.op_balance
  op_origin := hrem.op_origin
  op_caller := hrem.op_caller
  op_callvalue := hrem.op_callvalue
  op_calldataload := hrem.op_calldataload
  op_calldatasize := hrem.op_calldatasize
  op_calldatacopy := hrem.op_calldatacopy
  op_codesize := hrem.op_codesize
  op_codecopy := hrem.op_codecopy
  op_gasprice := hrem.op_gasprice
  op_extcodesize := hrem.op_extcodesize
  op_extcodecopy := hrem.op_extcodecopy
  op_returndatasize := hrem.op_returndatasize
  op_returndatacopy := hrem.op_returndatacopy
  op_extcodehash := hrem.op_extcodehash
  op_blockhash := hrem.op_blockhash
  op_coinbase := hrem.op_coinbase
  op_timestamp := hrem.op_timestamp
  op_number := hrem.op_number
  op_prevrandao := hrem.op_prevrandao
  op_gaslimit := hrem.op_gaslimit
  op_chainid := hrem.op_chainid
  op_selfbalance := hrem.op_selfbalance
  op_basefee := hrem.op_basefee
  op_blobhash := hrem.op_blobhash
  op_blobbasefee := hrem.op_blobbasefee
  op_slotnum := hrem.op_slotnum
  op_pop := hrem.op_pop
  op_mload := hrem.op_mload
  op_mstore := hrem.op_mstore
  op_mstore8 := hrem.op_mstore8
  op_sload := hrem.op_sload
  op_sstore := hrem.op_sstore
  op_jump := hrem.op_jump
  op_jumpi := hrem.op_jumpi
  op_pc := hrem.op_pc
  op_msize := hrem.op_msize
  op_gas := hrem.op_gas
  op_jumpdest := hrem.op_jumpdest
  op_tload := hrem.op_tload
  op_tstore := hrem.op_tstore
  op_push := hrem.op_push
  op_dup := hrem.op_dup
  op_swap := hrem.op_swap
  op_log := op_log_bounded_chain_spec
  op_dupn := hrem.op_dupn
  op_swapn := hrem.op_swapn
  op_exchange := hrem.op_exchange
  op_call := (opHandlerChainSpec_iff _).mp (op_call_chainSpecA hWc hgca)
  op_callcode := (opHandlerChainSpec_iff _).mp
    (op_callcode_chainSpecA hWc.toWorldAccountSpecsA hgca)
  op_staticcall := (opHandlerChainSpec_iff _).mp
    (op_staticcall_chainSpecA hWc.toWorldAccountSpecsA hgca)

/-- Full R29 chain-WF `op_dispatch` bundle assembling Group 09 (`op_return`, `op_revert`,
`op_mcopy`), all 7 Group 10 call/create opcodes (`Group10ChildBridge`), and bounded `op_log`
(`OpLogBridgeR29`). -/
theorem opDispatchChainHandlersCutover_of_r29
    (hWc : R16Shards.OpHandlersB.WorldAccountSpecsCall_g10)
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgcr : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create"))
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hrem : RemainingChainHandlersR29) :
    R16Shards.OpHandlersB.OpDispatchChainHandlersCutover :=
  opDispatchChainHandlersCutover_of_remaining
    hWc.toWorldAccountSpecsA hU hcc hcc2 hgcr hgca
    (remainingChainHandlersCutover_of_r29 hWc hgca hrem)

theorem op_dispatch_chain_spec_r29
    (hWc : R16Shards.OpHandlersB.WorldAccountSpecsCall_g10)
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgcr : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create"))
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hrem : RemainingChainHandlersR29) :
    R16Shards.OpHandlersB.HeadMemBridge.OpDispatchSpecA :=
  R16Shards.OpHandlersB.op_dispatch_chain_spec_cutover
    (opDispatchChainHandlersCutover_of_r29 hWc hU hcc hcc2 hgcr hgca hrem)

/-- End-to-end aligned `gbody_run_frames` bound with Group 09, all 7 Group 10 call/create
opcodes, bounded `op_log`, and `finish_child` / `frame_epilogue` / `frame_exception` wired. -/
theorem gbody_run_frames_aligned_r29
    (bf : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.FinishReadyA
      (ofString "finish_child") K.«finish_child»)
    (be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»)
    (bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»)
    (bd : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.EvmRunA
      (ofString "op_dispatch") K.«op_dispatch»)
    (hWc : R16Shards.OpHandlersB.WorldAccountSpecsCall_g10)
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgcr : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create"))
    (hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hrem : RemainingChainHandlersR29) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s)
      (ofString "run_frames") K.«run_frames» :=
  gbody_run_frames_aligned_of_chain_handlers bf be bx bd
    (opDispatchChainHandlersCutover_of_r29 hWc hU hcc hcc2 hgcr hgca hrem)

/-! ## 3. GuardedBody Phase 1 Backing Cut & Strong `gbody_process_transaction` -/

theorem ptxPhase1_backing_cut_full :
    type_of% @R13Shards.ptxPhase1_backing_cut_full :=
  R13Shards.ptxPhase1_backing_cut_full

theorem ptxPhase1_backing_cut :
    type_of% @R13Shards.ptxPhase1_backing_cut :=
  R13Shards.ptxPhase1_backing_cut

/-- Phase 1+2 backing cuts bundled once `PtxPhase1BackingCut` is discharged by
`PtxPhase1BackingCut.ptxPhase1_backing_cut`. -/
theorem ptxPhase12BackingCuts_of_r29
    (h1 : R13Shards.PtxCallees)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hp2 : R13Shards.PtxPhase2BackingCut) :
    R13Shards.PtxPhase12BackingCuts where
  phase1 := R13Shards.ptxPhase1_backing_cut h1 hent
  phase2 := hp2

/-- Cutover `gbody_process_transaction` on `TxReadyBackingStrong` with Phase 1 backing cut
discharged by `PtxPhase1BackingCut.ptxPhase1_backing_cut` and Phase 4 closed. -/
theorem gbody_process_transaction_backing_strong_r29
    (h : R16Shards.PtxCalleesCutover)
    (h1 : R13Shards.PtxCallees)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong)
    (hp2 : R13Shards.PtxPhase2BackingCut) :
    TerminatingFunBoundedOn
      R16Shards.TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  gbody_process_transaction_backing_strong_pmc_cutover_of_cuts h hwk hkeep
    (R13Shards.ptxPhase1_backing_cut h1 hent) hp2

/-! ## 4. Relational `wk_process_transaction` Strong Cuts (Phases 1, 2, 3, 5 Closed) -/

theorem ptxPhase1_relCut_strong :
    R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase1
      R16Shards.TopGbodyWk.PtxEntryFull R16Shards.TopGbodyWk.PtxAfterPhase1 :=
  R16Shards.TopGbodyWk.ptxPhase1_relCut_strong

theorem wk_process_message_call_marks_bo_of_callees :
    type_of% @R16Shards.TopGbodyWk.wk_process_message_call_marks_bo_of_callees :=
  R16Shards.TopGbodyWk.wk_process_message_call_marks_bo_of_callees

theorem ptxPhase3_relCut_strong :
    type_of% @R16Shards.TopGbodyWk.ptxPhase3_relCut_strong :=
  R16Shards.TopGbodyWk.ptxPhase3_relCut_strong

/-- `PtxPhase3` relational strong cut directly from `process_message` and
`process_create_message` Bo-marks contracts (`WkPmcMarksBo` + `WkPtxRelBasePhase3`). -/
theorem ptxPhase3_relCut_strong_of_callees
    (hpm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message")) :
    R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase3
      R16Shards.TopGbodyWk.PtxAfterPhase2 R16Shards.TopGbodyWk.PtxAfterPhase3 :=
  R16Shards.TopGbodyWk.ptxPhase3_relCut_strong
    (R16Shards.TopGbodyWk.wk_process_message_call_marks_bo_of_callees hpm hpcm)

/-- Full relational `wk_process_transaction` on `TxReadyStrong` closing:
- Phase 1 via `WkPtxPhase1.ptxPhase1_relCut_strong` (`PtxEntryFull`, no entry-loss),
- Phase 3 via `WkPtxRelBasePhase3.ptxPhase3_relCut_strong` + `WkPmcMarksBo`,
- Phase 5 via `StrongBridges.decode_witness_to_mpt_spec_wkBal`.
Only `hent` (`TxReadyStrong → TxReadyFullStrong`), `hdb`, `h2` (Phase 2 cut on
`TopGbodyWk.PtxAfterPhase1 → TopGbodyWk.PtxAfterPhase2`), `hpm`/`hpcm`
(`process_message` / `process_create_message` Bo-marks), and `h4` (Phase 4 cut)
remain as explicit hypotheses. -/
theorem wk_process_transaction_strong_r29
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      TxReadyStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (h2 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase2
      R16Shards.TopGbodyWk.PtxAfterPhase1 R16Shards.TopGbodyWk.PtxAfterPhase2)
    (hpm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message"))
    (h4 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase4
      R16Shards.TopGbodyWk.PtxAfterPhase3 R16Shards.TopGbodyWk.PtxAfterPhase4) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
        (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
        (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
        (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
        (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
        (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
        (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr",
       "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd =>
        RetTransactionLogs s r post S Nd ∧ R16Shards.TopGbodyWk.PtxRetSlices s r post S Nd)
      (ofString "process_transaction") :=
  wk_process_transaction_strong_of_witnessDb hdb
    R16Shards.TopGbodyWk.PtxEntryFull
    R16Shards.TopGbodyWk.PtxAfterPhase1
    R16Shards.TopGbodyWk.PtxAfterPhase2
    R16Shards.TopGbodyWk.PtxAfterPhase3
    (fun s hs => R16Shards.TopGbodyWk.txReadyFullStrong_init s (hent s hs))
    R16Shards.TopGbodyWk.ptxPhase1_relCut_strong
    h2
    (ptxPhase3_relCut_strong_of_callees hpm hpcm)
    h4

/-- Weakened `RetTransactionLogs` corollary matching the legacy `wk_process_transaction`
postcondition shape. -/
theorem wk_process_transaction_logs_r29
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      TxReadyStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (h2 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase2
      R16Shards.TopGbodyWk.PtxAfterPhase1 R16Shards.TopGbodyWk.PtxAfterPhase2)
    (hpm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message"))
    (h4 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase4
      R16Shards.TopGbodyWk.PtxAfterPhase3 R16Shards.TopGbodyWk.PtxAfterPhase4) :
    WorldKeeps TxReadyStrong
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
        (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
        (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
        (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
        (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
        (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
        (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr",
       "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      RetTransactionLogs (ofString "process_transaction") := by
  obtain ⟨ps, body, ret, hl, hb⟩ :=
    wk_process_transaction_strong_r29 hent hdb h2 hpm hpcm h4
  refine ⟨ps, body, ret, hl, fun s hc hP hex hnt hres => ?_⟩
  obtain ⟨hAp, hhp, hG, hK, hW⟩ := hb s hc hP hex hnt hres
  refine ⟨hAp, hhp, hG, hK, fun S Nd hWT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hOG, hFO, hQ⟩ := hW S Nd hWT hD
  exact ⟨S', Nd', hsub, hWT', hOG, hFO, hQ.1⟩

/-! ## 5. Builder, Withdrawals & System-Transaction Witness-DB Closures -/

theorem wkSc_idx_start_storage_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.builderBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra
      (ofString "idx_start_storage") :=
  R16Shards.TopGbodyWk.wkSc_idx_start_storage_of_decode_witness
    decode_witness_to_mpt_spec_wkBal hdb

theorem wk_idx_start_storage_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_storage") :=
  (wkSc_idx_start_storage_of_witnessDb hdb).to_worldKeeps

theorem wkSc_update_builder_from_tx_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.builderBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra
      (ofString "update_builder_from_tx") :=
  R16Shards.TopGbodyWk.wkSc_update_builder_from_tx_of_idx_storage
    (wkSc_idx_start_storage_of_witnessDb hdb)

theorem wkSc_process_withdrawals_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.withdrawalBufs)
      R16Shards.TopGbodyWk.withdrawalGlobals
      R16Shards.TopGbodyWk.withdrawalKeep NoExtra
      (ofString "process_withdrawals") :=
  R16Shards.TopGbodyWk.wkSc_process_withdrawals_of_decode_witness
    decode_witness_to_mpt_spec_wkBal hdb

private abbrev withdrawalC18Bufs : R16WkAcctWs.BufList :=
  [("bal_key_buf", 64), ("evm_key_buf", 32), ("keccak_pad", 136),
   ("keccak_st", 200), ("mpt_nib_scratch", 64), ("sk_buf", 52), ("u256_ws", 640)]

theorem wk_process_withdrawals_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_withdrawals") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := wkSc_process_withdrawals_of_witnessDb hdb
  have hwid : R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions withdrawalC18Bufs)
      R16Shards.TopGbodyWk.withdrawalGlobals
      R16Shards.TopGbodyWk.withdrawalKeep NoExtra
      (ofString "process_withdrawals") :=
    ⟨ps, body, ret, hl, fun s hc hW hex hnt hres =>
      R16Shards.TopGbodyWk.worldStepSc_mono_mask
        (B1 := R16Shards.TopGbodyWk.withdrawalBufs) (B2 := withdrawalC18Bufs)
        (by intro p hp
            simp only [R16Shards.TopGbodyWk.withdrawalBufs, withdrawalC18Bufs,
              List.mem_cons, List.not_mem_nil, or_false] at hp ⊢
            rcases hp with rfl | rfl | rfl | rfl | rfl <;> simp)
        (fun _ h => h)
        (fun rec hr k hk => ⟨rec.2, hr, hk⟩)
        (hb s hc hW hex hnt hres)⟩
  exact hwid.to_worldKeeps

theorem wkSc_incorporate_tx_into_block_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))) :
    R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.ptxIncorpBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals
      R16Shards.TopGbodyWk.ptxIncorpKeep NoExtra
      (ofString "incorporate_tx_into_block") :=
  R16Shards.TopGbodyWk.ptxIncorpKeeps_of_decode_witness
    decode_witness_to_mpt_spec_wkBal hdb

section SysTxClosure

open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.Wave8GuestInv.R10Shards.P26_P28
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs

private theorem ptxIncorpGlobals_sub_sysTx :
    ∀ g ∈ R16Shards.TopGbodyWk.ptxIncorpGlobals, g ∈ R16Shards.TopGbodyWk.sysTxGlobals := by
  intro g hg
  simp only [R16Shards.TopGbodyWk.ptxIncorpGlobals, R16Shards.TopGbodyWk.sysTxGlobals,
    List.mem_cons, List.not_mem_nil, or_false] at hg ⊢
  rcases hg with rfl | rfl | rfl | rfl <;> simp

private theorem worldKeeps_incSysTx_ptxIncorp_of_sc
    (hinc : WorldKeepsSc WorldOK
      (bufRegions R16Shards.TopGbodyWk.ptxIncorpBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals
      R16Shards.TopGbodyWk.ptxIncorpKeep NoExtra
      (ofString "incorporate_tx_into_block")) :
    WorldKeeps WorldOK
      (bufRegions R16Shards.TopGbodyWk.incSysTxBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals
      R16Shards.TopGbodyWk.sysTxKeep
      R16Shards.TopGbodyWk.RetSysTxIncorporate
      (ofString "incorporate_tx_into_block") := by
  obtain ⟨ps, body, ret, hl, hb⟩ := hinc
  refine ⟨ps, body, ret, hl, fun s hc hW hex hnt hres => ?_⟩
  obtain ⟨⟨hAp, hhp, hG, hK, hWT⟩, hsc⟩ := hb s hc hW hex hnt hres
  refine ⟨hAp, hhp, hG,
    R16Shards.TopGbodyWk.recordsKept_mono_keep
      R16Shards.TopGbodyWk.keepSub_sysTxKeep_freshTx hK,
    fun S Nd hT hD => ?_⟩
  obtain ⟨S', Nd', hsub, hT', hOG, hFO, _⟩ := hWT S Nd hT hD
  exact ⟨S', Nd', hsub, hT', hOG, hFO, hsc⟩

private theorem inc_sysTx_exc_worldStep_r29 {F : Type}
    {s0 s_pmc s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {w_m w_aa w_ak w_out : BitVec 64} {eid : MlS} {ev : ValueHOL 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : R16Shards.TopGbodyWk.SysTxMsgTablesStep s0 s_pmc w_m
      [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hstep : R16Shards.TopGbodyWk.SysTxPostPmcStep s_pmc none s w_m w_out)
    (hwstep : WorldStep (bufRegions R16Shards.TopGbodyWk.incSysTxBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals R16Shards.TopGbodyWk.sysTxKeep
      R16Shards.TopGbodyWk.RetSysTxIncorporate
      (callEntryStateHOLFinite s callee) (some (.exception eid ev)) cpost) :
    WorldStep (bufRegions R16Shards.TopGbodyWk.sysTxBufs)
      R16Shards.TopGbodyWk.sysTxGlobals R16Shards.TopGbodyWk.sysTxKeep NoExtra s0
      (some (.exception eid ev)) (emptyLocalsHOLFinite cpost) := by
  let ent := callEntryStateHOLFinite s callee
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, _, _, _, hW⟩ := hstep
  obtain ⟨hA_cp, hhp_cp, hG_cp, hK_cp, hW_cp⟩ := hwstep
  set post_ex : PanSemStateFiniteExact 64 F := emptyLocalsHOLFinite cpost
  have hA_ex : ArenaReady post_ex :=
    localsFree_arenaReady cpost HolFiniteMapExact.empty cpost.clock hA_cp
  have hG_ex : GlobalsKept R16Shards.TopGbodyWk.sysTxGlobals s_pmc post_ex := by
    intro k hk
    refine (hG k hk).trans (hG_cp k fun hm => ?_)
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, ptxIncorpGlobals_sub_sysTx g hg, rfl⟩)
  have hK_ex := R16Shards.TopGbodyWk.recordsKept_postPmc_trans_incSysTx hG hK hK_cp
  have hbuf_eq := R16Shards.TopGbodyWk.bufRegions_incSysTx_eq_of_postPmc hG
  refine R16Shards.TopGbodyWk.worldStep_of_msgTables_and_postPmc
    hW0 hmt hm152 hm160 hA_ex (le_trans hhp hhp_cp) hG_ex hK_ex
    (fun S Nd hWT hm152' hm160' hD => ?_)
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, _⟩ := hW S Nd hWT hm152' hm160' hD
  have hWT1_ent : WorldTypedWith ent S1 Nd1 :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S1).2 hWT1.1,
      hWT1.2.1, hWT1.2.2.1, hWT1.2.2.2.1, hWT1.2.2.2.2.1, hWT1.2.2.2.2.2⟩
  have hD1_ent : IvlsDisj (bufRegions R16Shards.TopGbodyWk.incSysTxBufs ent)
      (worldTypedIvls ent S1 Nd1) :=
    validBufList_disj R16Shards.TopGbodyWk.validBufList_incSysTxBufs hWT1_ent
  obtain ⟨S2, Nd2, hsub12, hWT2_cp, hOG12_cp, hFO12_cp, _⟩ := hW_cp S1 Nd1 hWT1_ent hD1_ent
  have hWT2 : WorldTypedWith post_ex S2 Nd2 :=
    ⟨(tablesTyped_with_locals cpost HolFiniteMapExact.empty cpost.clock S2).2 hWT2_cp.1,
      hWT2_cp.2.1, hWT2_cp.2.2.1, hWT2_cp.2.2.2.1, hWT2_cp.2.2.2.2.1, hWT2_cp.2.2.2.2.2⟩
  have hFO_tot :=
    R16Shards.TopGbodyWk.frameOutside_postPmc_trans_free_writes
      hA_pmc hAs hhp hfmp hsp hOG01 hFO01 hFO12_cp
      (fun i hi => by
        change i ∈ bufRegions R16Shards.TopGbodyWk.incSysTxBufs s at hi
        rw [hbuf_eq] at hi
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
        exact Or.inl ⟨bufferRegion s_pmc p,
          List.mem_cons_of_mem _ (List.mem_map.2
            ⟨p, R16Shards.TopGbodyWk.incSysTxBufs_sub_sysTxBufs p hp, rfl⟩),
          ⟨le_rfl, le_rfl⟩⟩)
  exact ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2,
    R16Shards.TopGbodyWk.ownedGrows_trans_sysTx hhp hhp_cp hOG01 hOG12_cp, hFO_tot⟩

private theorem inc_sysTx_ret_postStep_r29 {F : Type}
    {s0 s_pmc s cpost : PanSemStateFiniteExact 64 F}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)}
    {w_m w_aa w_ak w_out : BitVec 64} {v : ValueHOL 64}
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : R16Shards.TopGbodyWk.SysTxMsgTablesStep s0 s_pmc w_m
      [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hstep : R16Shards.TopGbodyWk.SysTxPostPmcStep s_pmc none s w_m w_out)
    (hwstep : WorldStep (bufRegions R16Shards.TopGbodyWk.incSysTxBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals R16Shards.TopGbodyWk.sysTxKeep
      R16Shards.TopGbodyWk.RetSysTxIncorporate
      (callEntryStateHOLFinite s callee) (some (.returned v)) cpost) :
    R16Shards.TopGbodyWk.SysTxPostPmcStep s_pmc none { cpost with locals := s.locals } w_m w_out := by
  let ent := callEntryStateHOLFinite s callee
  obtain ⟨_, S_u, Nd_u, hWT_u, hd_u⟩ :=
    R16Shards.TopGbodyWk.sysTxPostPmcStep_worldOK hW0 hmt hm152 hm160 hstep
  obtain ⟨hAs, hhp, hfmp, hsp, hG, hK, hw_out, hin_out, hmk, hW⟩ := hstep
  obtain ⟨hA_cp, hhp_cp, hG_cp, hK_cp, hW_cp⟩ := hwstep
  set s_inc : PanSemStateFiniteExact 64 F := { cpost with locals := s.locals }
  have hA_inc : ArenaReady s_inc := localsFree_arenaReady cpost s.locals cpost.clock hA_cp
  have hfmp_inc : globN s_inc "frame_mem_ptr" = globN s "frame_mem_ptr" :=
    R16Shards.globN_eq_of_lookup (s := s) (post := s_inc)
      (hG_cp (ofString "frame_mem_ptr") (by decide))
  have hG_inc : GlobalsKept R16Shards.TopGbodyWk.sysTxGlobals s_pmc s_inc := by
    intro k hk
    refine (hG k hk).trans (hG_cp k fun hm => ?_)
    obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hm
    exact hk (List.mem_map.2 ⟨g, ptxIncorpGlobals_sub_sysTx g hg, rfl⟩)
  have hK_inc := R16Shards.TopGbodyWk.recordsKept_postPmc_trans_incSysTx hG hK hK_cp
  have hbuf_eq := R16Shards.TopGbodyWk.bufRegions_incSysTx_eq_of_postPmc hG
  have hWT_u_ent : WorldTypedWith ent S_u Nd_u :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S_u).2 hWT_u.1,
      hWT_u.2.1, hWT_u.2.2.1, hWT_u.2.2.2.1, hWT_u.2.2.2.2.1, hWT_u.2.2.2.2.2⟩
  have hD_u_ent : IvlsDisj (bufRegions R16Shards.TopGbodyWk.incSysTxBufs ent)
      (worldTypedIvls ent S_u Nd_u) :=
    validBufList_disj R16Shards.TopGbodyWk.validBufList_incSysTxBufs hWT_u_ent
  obtain ⟨S_u', Nd_u', _, _, _, hFO_u, hsp_inc_le⟩ := hW_cp S_u Nd_u hWT_u_ent hD_u_ent
  have hlo_pmc : sourceBase ≤ globN s_pmc "heap_ptr" := hA_pmc.2.1
  have hin_s : Inside (w_out.toNat, 96) sourceBase (globN s "heap_ptr") :=
    ⟨le_trans hlo_pmc hin_out.1, hin_out.2⟩
  have hhp_lim : globN s "heap_ptr" ≤ heapLimit := hAs.2.2.1
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hin_bound : w_out.toNat + 96 ≤ 2 ^ 64 := by unfold Inside at hin_s; omega
  have hunhit_out : Wave8Contracts.M08.IvlUnhit s s_inc (w_out.toNat, 96) := by
    intro a ha8 ha1 ha2
    apply hFO_u a
    · intro j hj ⟨hc1, hc2⟩
      rcases List.mem_append.1 hj with hj12 | hfg
      · rcases List.mem_append.1 hj12 with hj_ow | hj_R
        · have hd_oj := hd_u (w_out.toNat, 96) (by simp) j hj_ow
          rcases j with ⟨j1, j2⟩
          by_cases hj2z : j2 = 0
          · have hj0 := R16Shards.TopGbodyWk.worldOwned_zero_base_sysTx hWT_u hj_ow hj2z
            cases hj0
            dsimp only at hc2; omega
          · rcases hd_oj with h0 | h0 | hle | hle <;> dsimp only at * <;> omega
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hj_R
          have hbr_eq : bufferRegion (callEntryStateHOLFinite s callee) p =
              bufferRegion s p := rfl
          rw [hbr_eq] at hc1 hc2
          by_cases hgz : globN s p.1 = 0
          · simp [bufferRegion, hgz] at hc2
          · obtain ⟨fsz, hgb, _, hle_sz⟩ := R16Shards.TopGbodyWk.validBufList_incSysTxBufs p hp
            have hp2_pos : 0 < p.2 := by
              simp only [R16Shards.TopGbodyWk.incSysTxBufs, List.mem_cons,
                List.not_mem_nil, or_false] at hp
              rcases hp with rfl | rfl | rfl | rfl | rfl <;> decide
            have hm_fo : (globN s p.1, fsz) ∈ worldOwned s S_u Nd_u := by
              apply List.mem_append_left; apply List.mem_append_right
              unfold fixedObjects
              apply List.mem_append_left; apply List.mem_append_left; apply List.mem_append_left
              have hm : (fun r : String × Nat => (globN s r.1, if globN s r.1 = 0 then 0 else r.2))
                  (p.1, fsz) ∈
                  globalBuffers.map (fun r => (globN s r.1, if globN s r.1 = 0 then 0 else r.2)) :=
                List.mem_map.2 ⟨(p.1, fsz), hgb, rfl⟩
              simpa [hgz] using hm
            have hd_ob := hd_u (w_out.toNat, 96) (by simp) (globN s p.1, fsz) hm_fo
            simp only [bufferRegion, hgz, ↓reduceIte] at hc1 hc2
            rcases hd_ob with h0 | h0 | hle | hle <;> dsimp only at * <;> omega
      · simp only [List.mem_singleton] at hfg
        subst j
        have hsep : heapLimit ≤ scratchStart := by decide
        have hfmp_ge : scratchStart ≤ globN s "frame_mem_ptr" := hAs.2.2.2.1
        have hfmp_ent : (freeGap (callEntryStateHOLFinite s callee)).1 = globN s "frame_mem_ptr" := rfl
        rw [hfmp_ent] at hc2
        unfold Inside at hin_s
        omega
    · intro ⟨hc1, _⟩
      change a.toNat + 8 > globN s "heap_ptr" at hc1
      unfold Inside at hin_s
      omega
  have hw_out_inc : WordsOK s_inc (w_out.toNat, 96) :=
    Wave8Contracts.M08.wordsOK_transfer hAs.1 hA_inc.1 hw_out
  have hm80 : memW s_inc (w_out.toNat + 80) = memW s (w_out.toNat + 80) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
      (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
  have hm88 : memW s_inc (w_out.toNat + 88) = memW s (w_out.toNat + 88) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
      (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
  have hm48 : memW s_inc (w_out.toNat + 48) = memW s (w_out.toNat + 48) :=
    Wave8Contracts.M08.memW_eq_of_ivlUnhit hunhit_out
      (by have := hw_out.1; omega) hin_bound ⟨by omega, by omega⟩
  refine ⟨hA_inc, le_trans hhp hhp_cp,
    by rw [hfmp_inc]; exact hfmp,
    le_trans hsp_inc_le hsp,
    hG_inc, hK_inc, hw_out_inc,
    ⟨hin_out.1, le_trans hin_out.2 hhp_cp⟩,
    by rw [hm80, hm88, hm48]; exact hmk,
    fun S Nd hWT hm152' hm160' hD => ?_⟩
  obtain ⟨S1, Nd1, hsub01, hWT1, hOG01, hFO01, hd_out1⟩ := hW S Nd hWT hm152' hm160' hD
  have hWT1_ent : WorldTypedWith ent S1 Nd1 :=
    ⟨(tablesTyped_with_locals s callee (s.clock - 1) S1).2 hWT1.1,
      hWT1.2.1, hWT1.2.2.1, hWT1.2.2.2.1, hWT1.2.2.2.2.1, hWT1.2.2.2.2.2⟩
  have hD1_ent : IvlsDisj (bufRegions R16Shards.TopGbodyWk.incSysTxBufs ent)
      (worldTypedIvls ent S1 Nd1) :=
    validBufList_disj R16Shards.TopGbodyWk.validBufList_incSysTxBufs hWT1_ent
  obtain ⟨S2, Nd2, hsub12, hWT2_cp, hOG12_cp, hFO12_cp, _⟩ := hW_cp S1 Nd1 hWT1_ent hD1_ent
  have hWT2 : WorldTypedWith s_inc S2 Nd2 :=
    ⟨(tablesTyped_with_locals cpost s.locals cpost.clock S2).2 hWT2_cp.1,
      hWT2_cp.2.1, hWT2_cp.2.2.1, hWT2_cp.2.2.2.1, hWT2_cp.2.2.2.2.1, hWT2_cp.2.2.2.2.2⟩
  have hFO_tot :=
    R16Shards.TopGbodyWk.frameOutside_postPmc_trans_free_writes
      hA_pmc hAs hhp hfmp hsp hOG01 hFO01 hFO12_cp
      (fun i hi => by
        change i ∈ bufRegions R16Shards.TopGbodyWk.incSysTxBufs s at hi
        rw [hbuf_eq] at hi
        obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hi
        exact Or.inl ⟨bufferRegion s_pmc p,
          List.mem_cons_of_mem _ (List.mem_map.2
            ⟨p, R16Shards.TopGbodyWk.incSysTxBufs_sub_sysTxBufs p hp, rfl⟩),
          ⟨le_rfl, le_rfl⟩⟩)
  refine ⟨S2, Nd2, fun t ht => hsub12 t (hsub01 t ht), hWT2,
    R16Shards.TopGbodyWk.ownedGrows_trans_sysTx hhp hhp_cp hOG01 hOG12_cp, hFO_tot, ?_⟩
  intro i hi o ho
  simp only [List.mem_singleton] at hi; subst i
  rcases hOG12_cp o ho with rfl | ⟨j, hj, hin_oj⟩ | hfresh
  · exact Wave8Contracts.M08.disj_zero_right _
  · exact Wave8Contracts.M08.disj_of_inside_right hin_oj
      (hd_out1 (w_out.toNat, 96) (by simp) j hj)
  · exact Or.inr (Or.inr (Or.inl (le_trans hin_out.2 hfresh.1)))

private theorem sysTxPostPmc_incorporate_step_r29 {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out : BitVec 64}
    (hinc : WorldKeeps WorldOK
      (bufRegions R16Shards.TopGbodyWk.incSysTxBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals
      R16Shards.TopGbodyWk.sysTxKeep
      R16Shards.TopGbodyWk.RetSysTxIncorporate
      (ofString "incorporate_tx_into_block"))
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : R16Shards.TopGbodyWk.SysTxMsgTablesStep s0 s_pmc w_m
      [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = GuestCodeLookup.originalRuntimeCode)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hstep : R16Shards.TopGbodyWk.SysTxPostPmcStep s_pmc none s w_m w_out)
    (hnt : (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes (evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])).1) :
    let res := evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") [])
    (WorldStep (bufRegions R16Shards.TopGbodyWk.sysTxBufs)
      R16Shards.TopGbodyWk.sysTxGlobals R16Shards.TopGbodyWk.sysTxKeep NoExtra s0 res.1 res.2 ∧
      ∃ eid ev, res.1 = some (.exception eid ev)) ∨
    (res.1 = none ∧
      R16Shards.TopGbodyWk.SysTxPostPmcStep s_pmc none res.2 w_m w_out ∧
      res.2.code = GuestCodeLookup.originalRuntimeCode ∧
      res.2.locals.lookup (ofString "out") = some (.val (.word w_out))) := by
  have hWs : WorldOK s :=
    (R16Shards.TopGbodyWk.sysTxPostPmcStep_worldOK hW0 hmt hm152 hm160 hstep).1
  have hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) [] = some [] := rfl
  rw [evaluateHOLFiniteState_call] at hnt hfr ⊢
  rw [hargs] at hnt hfr ⊢; dsimp only at hnt hfr ⊢
  rcases hlk : lookupCodeHOLFinite s.code.lookup (ofString "incorporate_tx_into_block") [] with
    _ | ⟨body', callee, ret'⟩
  · simp [hlk] at hfr; exact absurd hfr not_flowingOrResumes_error
  · simp only [hlk] at hnt hfr ⊢
    by_cases hz : s.clock = 0
    · simp [hz] at hnt
    · rw [if_neg hz] at hnt hfr ⊢
      let ent := callEntryStateHOLFinite s callee
      have hWent : WorldOK ent := localsFree_worldOK s callee (s.clock - 1) hWs
      have hmeta := (evaluateHOLFiniteState_metadata ent body').1
      rcases hrun : evaluateHOLFiniteState ent body' with ⟨res, cpost⟩
      simp only [ent] at hrun hmeta
      simp only [hrun] at hmeta hnt hfr ⊢
      have hnt_c : (evaluateHOLFiniteState ent body').1 ≠ some .timeOut := by
        simp only [ent, hrun]; rintro rfl; simp at hnt
      cases res with
      | none => exact absurd hfr not_flowingOrResumes_error
      | some cr =>
        cases cr with
        | timeOut => simp at hnt
        | error | «break» | «continue» => exact absurd hfr not_flowingOrResumes_error
        | finalFfi _ => exact absurd hfr not_flowingOrResumes_finalFfi
        | exception eid ev =>
          left
          dsimp only at hfr ⊢
          have hres_ex : Resumes (some (.exception eid ev)) := by
            rcases hfr with h | h | h | hr <;> try simp at h
            exact hr
          have hspec := FunSpec.at_lookup hinc s hc [] body' callee ret' hlk hWent hnt_c
          simp only [hrun] at hspec
          exact ⟨inc_sysTx_exc_worldStep_r29 hW0 hA_pmc hmt hm152 hm160 hstep (hspec hres_ex),
            eid, ev, rfl⟩
        | returned v =>
          dsimp only at hnt hfr ⊢
          by_cases hsh : shapeEqHOL (shapeOfHOLExact v) ret' = true
          · right
            simp only [hsh, ↓reduceIte] at hnt hfr ⊢
            have hspec := FunSpec.at_lookup hinc s hc [] body' callee ret' hlk hWent hnt_c
            simp only [hrun] at hspec
            have hstep_inc := inc_sysTx_ret_postStep_r29 hW0 hA_pmc hmt hm152 hm160 hstep
              (hspec (Or.inl ⟨v, rfl⟩))
            have hcode_inc : ({ cpost with locals := s.locals } : PanSemStateFiniteExact 64 F).code =
                GuestCodeLookup.originalRuntimeCode := by
              dsimp only; rw [hmeta]; exact hc
            exact ⟨trivial, hstep_inc, hcode_inc, hl_out⟩
          · simp [hsh] at hfr; exact absurd hfr not_flowingOrResumes_error

private theorem sysTxPmcCont_step_r29 {F : Type}
    {s0 s_pmc s : PanSemStateFiniteExact 64 F}
    {w_m w_aa w_ak w_out : BitVec 64}
    (hinc : WorldKeeps WorldOK
      (bufRegions R16Shards.TopGbodyWk.incSysTxBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals
      R16Shards.TopGbodyWk.sysTxKeep
      R16Shards.TopGbodyWk.RetSysTxIncorporate
      (ofString "incorporate_tx_into_block"))
    (hW0 : WorldOK s0)
    (hA_pmc : ArenaReady s_pmc)
    (hmt : R16Shards.TopGbodyWk.SysTxMsgTablesStep s0 s_pmc w_m
      [(w_aa.toNat, 20), (w_ak.toNat, 52)])
    (hm152 : memW s_pmc (w_m.toNat + 152) = w_aa.toNat)
    (hm160 : memW s_pmc (w_m.toNat + 160) = w_ak.toNat)
    (hc : s.code = GuestCodeLookup.originalRuntimeCode)
    (hl_out : s.locals.lookup (ofString "out") = some (.val (.word w_out)))
    (hstep : R16Shards.TopGbodyWk.SysTxPostPmcStep s_pmc none s w_m w_out)
    (hnt : (evaluateHOLFiniteState s R16Shards.TopGbodyWk.sysTxPmcCont).1 ≠ some .timeOut)
    (hfr : FlowingOrResumes
      (evaluateHOLFiniteState s R16Shards.TopGbodyWk.sysTxPmcCont).1) :
    WorldStep (bufRegions R16Shards.TopGbodyWk.sysTxBufs)
      R16Shards.TopGbodyWk.sysTxGlobals R16Shards.TopGbodyWk.sysTxKeep NoExtra s0
      (evaluateHOLFiniteState s R16Shards.TopGbodyWk.sysTxPmcCont).1
      (evaluateHOLFiniteState s R16Shards.TopGbodyWk.sysTxPmcCont).2 := by
  unfold R16Shards.TopGbodyWk.sysTxPmcCont at hnt hfr ⊢
  rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_skip] at hnt hfr ⊢
  dsimp only at hnt hfr ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hnt hfr ⊢
  rcases hrun : evaluateHOLFiniteState s
      (.call (some (none, none)) (ofString "incorporate_tx_into_block") []) with ⟨r1, mid⟩
  simp only [hrun] at hnt hfr ⊢
  cases r1 with
  | none =>
    have hinc_step := sysTxPostPmc_incorporate_step_r29
      hinc hW0 hA_pmc hmt hm152 hm160 hc hl_out hstep
      (by rw [hrun]; simp) (by rw [hrun]; exact Or.inl rfl)
    dsimp only at hinc_step
    rw [hrun] at hinc_step
    rcases hinc_step with ⟨_, eid, ev, hex⟩ | ⟨_, hstep_mid, hc_mid, hl_out_mid⟩
    · cases hex
    · exact R16Shards.TopGbodyWk.sysTxAfterIncorporate_step
        hW0 hA_pmc hmt hm152 hm160 hc_mid hl_out_mid hstep_mid hnt hfr
  | some cr =>
    have hinc_step := sysTxPostPmc_incorporate_step_r29
      hinc hW0 hA_pmc hmt hm152 hm160 hc hl_out hstep
      (by rw [hrun]; exact hnt) (by rw [hrun]; exact hfr)
    dsimp only at hinc_step
    rw [hrun] at hinc_step
    rcases hinc_step with ⟨hwStep, _⟩ | ⟨hnone, _⟩
    · exact hwStep
    · cases hnone

/-- `wk_process_unchecked_system_transaction` closed through `incorporate_tx_into_block`
from `decode_witness_to_mpt_spec_wkBal` (eliminating the `hinc` premise completely). -/
theorem wk_process_unchecked_system_transaction_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) ::
        bufRegions R16Shards.TopGbodyWk.pmcSysTxBufs s)
      R16Shards.TopGbodyWk.pmcSysTxGlobals R16Shards.TopGbodyWk.pmcSysTxKeep
      R16Shards.TopGbodyWk.RetSysTxPmc (ofString "process_message_call")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
       "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_unchecked_system_transaction") := by
  have hinc := worldKeeps_incSysTx_ptxIncorp_of_sc
    (wkSc_incorporate_tx_into_block_of_witnessDb hdb)
  refine ⟨_, _, _, R16Shards.TopGbodyWk.lookup_process_unchecked_system_transaction,
    fun s0 hc0 hW0 ⟨vals, hlk⟩ hnt0 hres0 => ?_⟩
  obtain ⟨wt, wd, wdn, hl_t0, hl_d0, hl_dn0⟩ :=
    R16Shards.TopGbodyWk.lookupCode_unchecked_sysTx_words hlk
  have hfr0 : FlowingOrResumes
      (evaluateHOLFiniteState s0
        (sourceFnBody Guest.Software.guestFn_process_unchecked_system_transaction)).1 :=
    Or.inr (Or.inr (Or.inr hres0))
  rcases R16Shards.TopGbodyWk.prefix_unchecked_sysTx_to_pmc
      s0 hc0 hW0 wt wd wdn hl_t0 hl_d0 hl_dn0 hnt0 hfr0 with
    ⟨hp_ex, _⟩ |
    ⟨s_pmc, w_m, w_aa, w_ak, L_wrap, hmt, hW_pmc, hc_pmc, hl_m, hm152, hm160, hmsg,
      hnt_pmc, hfr_pmc, hr_eq, hs_eq⟩
  · exact hp_ex.1
  · rcases R16Shards.TopGbodyWk.pmc_decCall_sysTx_step
        hW0 hmt hW_pmc hc_pmc hl_m hm152 hm160 hmsg hpmc hnt_pmc hfr_pmc with
      ⟨hw_ex, _⟩ | ⟨w_out, s1, hstep1, hc1, hl_out1, hnt1, hfr1, hr1, hs1⟩
    · rw [hr_eq, hs_eq]
      exact R16Shards.TopGbodyWk.worldStep_with_locals_clock hw_ex _ _
    · have hw_cont := sysTxPmcCont_step_r29
        hinc hW0 hW_pmc.1 hmt hm152 hm160 hc1 hl_out1 hstep1 hnt1 hfr1
      rw [hr_eq, hs_eq, hr1, hs1]
      exact R16Shards.TopGbodyWk.worldStep_with_locals_clock hw_cont _ _

end SysTxClosure

theorem wk_process_checked_system_transaction_of_witnessDb
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) ::
        R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.pmcSysTxBufs s)
      R16Shards.TopGbodyWk.pmcSysTxGlobals R16Shards.TopGbodyWk.pmcSysTxKeep
      R16Shards.TopGbodyWk.RetSysTxPmc (ofString "process_message_call")) :
    WorldKeeps WorldOK
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
                 (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
                 (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
                 (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
                 (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
                 (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
                 (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
                 (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
                 (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
                 (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
                 (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
                 (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
                 (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
                 (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
                 (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
                 (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr", "heap_ptr",
       "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "process_checked_system_transaction") :=
  R16Shards.TopGbodyWk.«wk_process_checked_system_transaction_of_unchecked»
    (wk_process_unchecked_system_transaction_of_witnessDb hdb hpmc)

/-! ## 6. TopGbodyWk, MptRoot, and SetCode R29 Strong Exports -/

theorem gbody_payload_header : GBody.«payload_header» :=
  R16Shards.TopGbodyWk.«gbody_payload_header»

theorem wk_block_rlp_length_strong :
    WorldKeeps (fun s => WorldOK s ∧ HeaderOK s) (fun _ => [])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "block_rlp_length") :=
  R16Shards.TopGbodyWk.«wk_block_rlp_length»

theorem wk_decode_host_input_strong_sound :
    type_of% @R16Shards.TopGbodyWk.wk_decode_host_input_strong_sound :=
  R16Shards.TopGbodyWk.wk_decode_host_input_strong_sound

theorem wk_decode_host_input_of_nonempty :
    type_of% @R16Shards.TopGbodyWk.wk_decode_host_input_of_nonempty :=
  R16Shards.TopGbodyWk.wk_decode_host_input_of_nonempty

theorem wk_encode_transaction_bounded :
    type_of% @R16Shards.TopGbodyWk.«wk_encode_transaction_bounded» :=
  R16Shards.TopGbodyWk.«wk_encode_transaction_bounded»

theorem wk_check_transaction_bo :
    type_of% @R16Shards.TopGbodyWk.«wk_check_transaction_bo» :=
  R16Shards.TopGbodyWk.«wk_check_transaction_bo»

theorem wk_recover_sender_with_chain_id_bo :
    type_of% @R16Shards.TopGbodyWk.«wk_recover_sender_with_chain_id_bo» :=
  R16Shards.TopGbodyWk.«wk_recover_sender_with_chain_id_bo»

theorem wk_requests_append :
    type_of% @R16Shards.TopGbodyWk.«wk_requests_append» :=
  R16Shards.TopGbodyWk.«wk_requests_append»

theorem eval_call_mpt_root_fresh :
    type_of% @R16Shards.TopGbodyWk.eval_call_mpt_root_fresh :=
  R16Shards.TopGbodyWk.eval_call_mpt_root_fresh

theorem funSpec_set_code_msgBounded :
    type_of% @R16Shards.EvmEkFk.funSpec_set_code_msgBounded :=
  R16Shards.EvmEkFk.funSpec_set_code_msgBounded

theorem fk_set_code_msgBounded :
    type_of% @R16Shards.EvmEkFk.fk_set_code_msgBounded :=
  R16Shards.EvmEkFk.fk_set_code_msgBounded

theorem hoare_d0PreB_call_set_code :
    type_of% @R16Shards.EvmEkFk.hoare_d0PreB_call_set_code :=
  R16Shards.EvmEkFk.hoare_d0PreB_call_set_code

end InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
