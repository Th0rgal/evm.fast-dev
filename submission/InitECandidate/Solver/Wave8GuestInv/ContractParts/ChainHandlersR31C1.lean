import InitECandidate.Solver.Wave8GuestInv.PrimitivesProved
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C09
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C12
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C13
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C15
import InitECandidate.Solver.Wave8GuestInv.ContractParts.C16
import InitECandidate.Solver.Wave8GuestInv.R16Shards.PrimC08Closure
import InitECandidate.Solver.Wave8GuestInv.Deliveries.GBODY_RUNFRAMES_SOL.OpDispatch
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemAlignedBridge

/-! # Wave 8 R31 Chain Handlers (C1) — `ChainHandlersR31Stmt` bounded-entry fields

Closes the four `TerminatingFunBoundedOn` fields of `StrongBridgesR31.ChainHandlersR31Stmt`
from clean (0-gap) unconditional leaves, applying each `GBody` bundle to its
callee arguments exactly as `Assembly.assembly_main` does, but citing only clean leaves
(the legacy-stub `wk_decode_host_input` primitive is never used).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31C1

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

/-- `g_ws_storage_trie` sub-chain (clean leaves only). -/
theorem g_decode_witness_to_mpt_r31 :
    TerminatingFunBoundedOn (fun {F} => ArenaReady) (ofString "decode_witness_to_mpt")
      K.decode_witness_to_mpt :=
  «gbody_decode_witness_to_mpt»
    («gbody__decode_witness_node»
      («gbody__decode_witness_node_mpt»
        (R16Shards.PrimC08Closure.«gbody__decode_witness_node_body»
          R11Adapters.«fb__decode_step» R11Adapters.«fb__resolve_step»
          Merged.fb_mpt_fail Merged.fb_node_new_ext PrimShardP10P30.fb_rlp_item
          R16Shards.MptC10C12.«ww__decode_step» R16Shards.MptC10C12.«sp__decode_step»
          R16Shards.ResolveDecodeStep.«ww__resolve_step» R16Shards.ResolveDecodeStep.«sp__resolve_step»
          R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» R10Shards.P02.ww_node_new_ext
          R16Shards.«rt_node_new_ext» R10Shards.P02.ww_rlp_item)
        Merged.fb_scratch_release)
      Merged.fb_scratch_mark Merged.fb_scratch_release R10Shards.P02.ro_scratch_mark)
    Merged.fb_alloc Merged.fb_memcpy Merged.fb_memeq Merged.fb_mpt_fail
    Merged.fb_nodedb_lookup Wave8Contracts.M15.«ro_memeq»
    R11Adapters.ReadOnlyLeaves.«ro_mpt_fail» R11Adapters.ReadOnlyLeaves.«ro_nodedb_lookup»

theorem g_ws_get_storage_r31 :
    TerminatingFunBoundedOn (fun {F} => WorldOK) (ofString "ws_get_storage")
      K.ws_get_storage :=
  «gbody_ws_get_storage» Merged.fb_alloc PrimShardP10P30.fb_heap_mark
    PrimShardP10P30.fb_heap_release PrimShardP10P30.fb_keccak256 Merged.fb_memeq
    PrimShardP10P30.fb_rlp_decode_fully Merged.fb_trie_lookup
    P12_P15.Callees.fb_u256_from_be R11Adapters.«fb_ws_storage_root_of»
    («gbody_ws_storage_trie» g_decode_witness_to_mpt_r31 Merged.fb_htab_get
      Merged.fb_htab_set Wave8Contracts.M15.«ro_htab_get»)
    Wave8Contracts.M15.«ro_memeq» R13Shards.WkShard01.«wk_ws_storage_root_of»

theorem g_get_storage_r31 :
    TerminatingFunBoundedOn (fun {F} => WorldOK) (ofString "get_storage") K.get_storage :=
  R16Shards.PrimC08Closure.«gbody_get_storage» Merged.fb_htab_set
    Merged.fb_record_pre_state_read PrimShardP10P30.fb_sk_make
    (Wave8Leaves.S03.fb_stor_lookup Merged.fb_htab_get) g_ws_get_storage_r31
    R16Shards.PrimC08Closure.htab_set_spec EvmFrameSpecs.nz_htab_set
    R16Shards.«wk_record_pre_state_read» EvmFrameSpecs.wk_sk_make M17.«ro_stor_lookup»

theorem g_get_storage_original_r31 :
    TerminatingFunBoundedOn (fun {F} => WorldOK) (ofString "get_storage_original")
      K.get_storage_original :=
  «gbody_get_storage_original» Merged.fb_htab_has Merged.fb_record_pre_state_read
    (Wave8Leaves.S03.fb_stor_lookup Merged.fb_htab_get) g_ws_get_storage_r31
    Wave8Contracts.M15.«ro_htab_has» R16Shards.«wk_record_pre_state_read» M17.«ro_stor_lookup»

theorem g_op_sload_r31 :
    TerminatingFunBoundedOn EvmRun (ofString "op_sload") K.«op_sload» :=
  R16Shards.PrimC08Closure.«gbody_op_sload» P12_P15.Callees.fb_charge_gas g_get_storage_r31
    R11Adapters.«fb_is_warm_storage_key» Merged.fb_pc_add Merged.fb_stack_pop
    Merged.fb_stack_push R10Shards.P10.fb_u256_to_be32 PrimShardP10P30.fb_warm_storage_key
    EvmFrameSpecs.ek_charge_gas EvmFrameSpecs.ek_is_warm_storage_key
    EvmFrameSpecs.ek_stack_pop EvmFrameSpecs.ek_u256_to_be32
    R16Shards.EvmEkFk.«ek_warm_storage_key»

/-- The one remaining legacy placeholder (`ContractParts.C08.lean:74`, legacy stub):
the weak-guard `get_storage_original` Evm-keeps contract required by the
`op_sstore` callee bundle (`GBody.«op_sstore»` slot). Parameterized here so the
R32/S1b Pillar-2 lane can plug in its clean proof; every other leaf of the
`bd` chain is closed unconditionally. -/
theorem g_op_sstore_r31
    (hkgso : EvmKeeps (EvmAvoids (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]))
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original")) :
    TerminatingFunBoundedOn EvmRun (ofString "op_sstore") K.«op_sstore» :=
  R16Shards.PrimC08Closure.«gbody_op_sstore» P12_P15.Callees.fb_charge_gas
    (Wave8Leaves.S03.fb_charge_state_gas P12_P15.Callees.fb_add_sat) Merged.fb_check_gas
    Merged.fb_credit_state_gas_refund g_get_storage_r31 g_get_storage_original_r31
    R11Adapters.«fb_is_warm_storage_key» R10Shards.P10.fb_max Merged.fb_pc_add
    Merged.fb_require_not_static PrimShardP10P30.fb_set_storage Merged.fb_stack_pop
    R11Adapters.«fb_u256_eq» P12_P15.Callees.fb_u256_is_zero R10Shards.P10.fb_u256_to_be32
    PrimShardP10P30.fb_warm_storage_key EvmFrameSpecs.ek_charge_gas R10Ports.ro_check_gas
    hkgso EvmFrameSpecs.ek_is_warm_storage_key Wave8Contracts.M15.«ro_max»
    R10Shards.P10.ro_require_not_static EvmFrameSpecs.ek_stack_pop
    EvmFrameSpecs.ek_u256_to_be32 R16Shards.EvmEkFk.«ek_warm_storage_key»

theorem bd_op_dispatch_r31
    (hkgso : EvmKeeps (EvmAvoids (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]))
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original")) :
    TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.EvmRunA
      (ofString "op_dispatch") K.«op_dispatch» := by
  have hbd := Merged.gbody_op_dispatch
    R11Adapters.«fb_op_add» R11Adapters.Closure4.«fb_op_addmod» R11Adapters.«fb_op_address»
    Merged.fb_op_and R11Adapters.«fb_op_balance» Merged.fb_op_basefee
    R11Adapters.«fb_op_blobbasefee» R11Adapters.«fb_op_blobhash» R11Adapters.«fb_op_blockhash»
    R11Adapters.«fb_op_byte» R11Adapters.StaticCall.«fb_op_call»
    R11Adapters.StaticCall.«fb_op_callcode» R11Adapters.«fb_op_calldatacopy»
    R11Adapters.«fb_op_calldataload» R11Adapters.«fb_op_calldatasize» R11Adapters.«fb_op_caller»
    P12_P15.fb_op_callvalue P12_P15.fb_op_chainid P12_P15.fb_op_clz P12_P15.fb_op_codecopy
    P12_P15.fb_op_codesize R11Adapters.«fb_op_coinbase» Merged.fb_op_create
    Merged.fb_op_create2 Merged.fb_op_delegatecall R11Adapters.«fb_op_div» Merged.fb_op_dup
    Merged.fb_op_dupn R11Adapters.«fb_op_eq» R11Adapters.«fb_op_exchange»
    R11Adapters.«fb_op_exp» R11Adapters.«fb_op_extcodecopy» R11Adapters.«fb_op_extcodehash»
    R11Adapters.«fb_op_extcodesize» Merged.fb_op_gas Merged.fb_op_gaslimit
    Merged.fb_op_gasprice R11Adapters.«fb_op_gt» R11Adapters.«fb_op_iszero» Merged.fb_op_jump
    P12_P15.fb_op_jumpdest P12_P15.fb_op_jumpi P13.fb_op_keccak P13.fb_op_log P13.fb_op_lt
    P13.fb_op_mcopy P13.fb_op_mload P13.fb_op_mod P13.fb_op_msize R11Adapters.«fb_op_mstore»
    R11Adapters.«fb_op_mstore8» R11Adapters.«fb_op_mul» R11Adapters.Closure4.«fb_op_mulmod»
    R11Adapters.«fb_op_not» R11Adapters.«fb_op_number» R11Adapters.«fb_op_or»
    P12_P15.fb_op_origin P12_P15.fb_op_pc P12_P15.fb_op_pop R11Adapters.«fb_op_prevrandao»
    P12_P15.fb_op_push P12_P15.fb_op_return P12_P15.fb_op_returndatacopy
    Merged.fb_op_returndatasize P12_P15.fb_op_revert R11Adapters.«fb_op_sar»
    R11Adapters.«fb_op_sdiv» R11Adapters.«fb_op_selfbalance» R11Adapters.«fb_op_selfdestruct»
    R11Adapters.«fb_op_sgt» R11Adapters.«fb_op_shl» R11Adapters.«fb_op_shr»
    R11Adapters.«fb_op_signextend» g_op_sload_r31 Merged.fb_op_slotnum
    R11Adapters.«fb_op_slt» R11Adapters.«fb_op_smod» (g_op_sstore_r31 hkgso)
    R11Adapters.StaticCall.«fb_op_staticcall» Merged.fb_op_stop
    R11Adapters.«fb_op_sub» Merged.fb_op_swap Merged.fb_op_swapn Merged.fb_op_timestamp
    R11Adapters.«fb_op_tload» R11Adapters.«fb_op_tstore» Merged.fb_op_xor
  exact R16Shards.OpHandlersB.HeadMemBridge.evmRunA_bound hbd

theorem bf_finish_child_r31 :
    TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.FinishReadyA
      (ofString "finish_child") K.«finish_child» := by
  have hfc := R16Shards.PrimC08Closure.«gbody_finish_child»
    P12_P15.Callees.fb_address_to_u256 R11Adapters.«fb_create_finish»
    Merged.fb_credit_state_gas_refund Wave8Leaves.S03.fb_frame_halt
    Wave8Leaves.S03.fb_frame_mem_release Merged.fb_incorporate_child_on_error
    Merged.fb_incorporate_child_on_success Merged.fb_memcpy R11Adapters.«fb_min»
    Merged.fb_pc_add Merged.fb_refill_frame_state_gas
    (R16Shards.PrimC08Closure.«gbody_rollback_child_access»
      (R16Shards.PrimC08Closure.«gbody_htab_truncate» Merged.fb_htab_del
        Merged.htab_del_spec Merged.htab_del_progress_spec)
      HtabC00Ports.htab_truncate_spec)
    Merged.fb_scratch_release Merged.fb_set_retdata Merged.fb_stack_push
    Merged.fb_state_restore R16Shards.EvmEkFk.«ek_create_finish» EvmFrameSpecs.ek_frame_halt
    EvmFrameSpecs.ek_refill_frame_state_gas R16Shards.StateRestoreEpilogue.ek_state_restore
  exact R16Shards.OpHandlersB.HeadMemBridge.finishReadyA_bound hfc

/-- `be`: the `frame_epilogue` bound (clean `Merged` leaf). -/
theorem be_frame_epilogue_r31 :
    TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue» :=
  Merged.fb_frame_epilogue

/-- `bx`: the `frame_exception` bound (clean `Merged` leaf). -/
theorem bx_frame_exception_r31 :
    TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception» :=
  Merged.fb_frame_exception

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31C1
