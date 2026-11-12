import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.SetStorageR31
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31C1
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C4
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C5
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallR32
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CreateR32

/-! # Wave 8 R32 Chain Handlers (`ChainHandlersR32C`) — assembly

Closes `StrongBridgesR32.ChainHandlersR32Stmt` (StrongBridgesR32.lean:596) with
every lane that already has an unconditional proof, and states the remaining
obligations as explicit, individually named premises:

* **Closed unconditionally**: `hsetA` (`SetStorageR31.epsA_set_storage_r31`,
  already proved unconditionally), and the three frame bounds `bf`, `be`, `bx`
  (`ChainHandlersR31C1`). The fourth bound `bd` closes modulo the single
  witness-DB premise `hdb : HdbBounded`, from which the legacy
  `get_storage_original` Evm-keeps contract (`hkgso`) is discharged by
  `StorageCreateFinish.ek_get_storage_original_of_decode_witness` with the
  unconditional decode-witness spec
  (`StrongBridges.decode_witness_to_mpt_spec`, StorageCreateFinish.lean:23756).
* **Premises (clean parameters)**: the five Group 10 callee contracts at
  `EvmPreservingSpecAR32` strength (`hU`, `hcc`, `hcc2`, `hgcr`, `hgca`), the
  ten call/create-family chain-WF handlers (`hop_*`; the six G10 ops are
  derived from the `Group10CreateR32`/`Group10CallR32` A-strength specs via
  `CallSpecLiftR32` — see `hop_create_of_g10` etc. below), the 23 remaining
  opcode walks (`RemainingChainHandlersR32C4`, merged with the 54 proved
  fields of `ChainHandlersR32C2`/`C3` by `remainingChainHandlersR32_of`), and
  the R32-aligned `run_frames` bound (`hframes`).
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

/-! ## 1. The `bd` witness-DB premise -/

/-- Witness-DB bound parameter (same statement as
`StrongBridgesPtxBridgeR31.HdbBounded` / `WkPtxClosureR32.HdbBounded`): under
`WorldOK` with a non-null `ws` global, the node-DB slices reachable from
`memW s ws` are bounded. This is the single premise behind the
`get_storage_original` Evm-keeps discharge of `bd`. -/
abbrev HdbBounded : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    WorldOK s → globN s "ws" ≠ 0 →
      R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))

/-- The legacy `get_storage_original` Evm-keeps contract (`hkgso` of
`ChainHandlersR31C1.bd_op_dispatch_r31`), discharged from the unconditional
decode-witness spec and the witness-DB bound. -/
theorem hkgso_of_hdb (hdb : HdbBounded) :
    EvmKeeps (EvmAvoids (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]))
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original") :=
  R16Shards.EvmEkFk.StorageCreateFinish.ek_get_storage_original_of_decode_witness
    decode_witness_to_mpt_spec hdb

/-! ## 2. The 77-field remaining bundle -/

/-- The full 77-field `RemainingChainHandlersR32`, merging the 54 walks proved
in `ChainHandlersR32C2` (52) and `ChainHandlersR32C3` (`op_jump`, `op_jumpi`),
the three swap walks of `ChainHandlersR32C4` (`op_swap`, `op_swapn`,
`op_exchange`), the `op_selfbalance` walk of `ChainHandlersR32C5`, and the 19
still-open fields of `ChainHandlersR32C5.RemainingChainHandlersR32C5`. -/
theorem remainingChainHandlersR32_of (hc5 : ChainHandlersR32C5.RemainingChainHandlersR32C5) :
    RemainingChainHandlersR32 where
  op_stop := ChainHandlersR32C2.op_stop_chainSpecR32
  op_add := ChainHandlersR32C2.op_add_chainSpecR32
  op_mul := ChainHandlersR32C2.op_mul_chainSpecR32
  op_sub := ChainHandlersR32C2.op_sub_chainSpecR32
  op_div := ChainHandlersR32C2.op_div_chainSpecR32
  op_sdiv := ChainHandlersR32C2.op_sdiv_chainSpecR32
  op_mod := ChainHandlersR32C2.op_mod_chainSpecR32
  op_smod := ChainHandlersR32C2.op_smod_chainSpecR32
  op_addmod := ChainHandlersR32C2.op_addmod_chainSpecR32
  op_mulmod := ChainHandlersR32C2.op_mulmod_chainSpecR32
  op_exp := ChainHandlersR32C2.op_exp_chainSpecR32
  op_signextend := ChainHandlersR32C2.op_signextend_chainSpecR32
  op_lt := ChainHandlersR32C2.op_lt_chainSpecR32
  op_gt := ChainHandlersR32C2.op_gt_chainSpecR32
  op_slt := ChainHandlersR32C2.op_slt_chainSpecR32
  op_sgt := ChainHandlersR32C2.op_sgt_chainSpecR32
  op_eq := ChainHandlersR32C2.op_eq_chainSpecR32
  op_iszero := ChainHandlersR32C2.op_iszero_chainSpecR32
  op_and := ChainHandlersR32C2.op_and_chainSpecR32
  op_or := ChainHandlersR32C2.op_or_chainSpecR32
  op_xor := ChainHandlersR32C2.op_xor_chainSpecR32
  op_not := ChainHandlersR32C2.op_not_chainSpecR32
  op_byte := ChainHandlersR32C2.op_byte_chainSpecR32
  op_shl := ChainHandlersR32C2.op_shl_chainSpecR32
  op_shr := ChainHandlersR32C2.op_shr_chainSpecR32
  op_sar := ChainHandlersR32C2.op_sar_chainSpecR32
  op_clz := ChainHandlersR32C2.op_clz_chainSpecR32
  op_keccak := hc5.op_keccak
  op_address := ChainHandlersR32C2.op_address_chainSpecR32
  op_balance := hc5.op_balance
  op_origin := ChainHandlersR32C2.op_origin_chainSpecR32
  op_caller := ChainHandlersR32C2.op_caller_chainSpecR32
  op_callvalue := ChainHandlersR32C2.op_callvalue_chainSpecR32
  op_calldataload := hc5.op_calldataload
  op_calldatasize := ChainHandlersR32C2.op_calldatasize_chainSpecR32
  op_calldatacopy := hc5.op_calldatacopy
  op_codesize := ChainHandlersR32C2.op_codesize_chainSpecR32
  op_codecopy := hc5.op_codecopy
  op_gasprice := ChainHandlersR32C2.op_gasprice_chainSpecR32
  op_extcodesize := hc5.op_extcodesize
  op_extcodecopy := hc5.op_extcodecopy
  op_returndatasize := ChainHandlersR32C2.op_returndatasize_chainSpecR32
  op_returndatacopy := hc5.op_returndatacopy
  op_extcodehash := hc5.op_extcodehash
  op_blockhash := hc5.op_blockhash
  op_coinbase := ChainHandlersR32C2.op_coinbase_chainSpecR32
  op_timestamp := ChainHandlersR32C2.op_timestamp_chainSpecR32
  op_number := ChainHandlersR32C2.op_number_chainSpecR32
  op_prevrandao := ChainHandlersR32C2.op_prevrandao_chainSpecR32
  op_gaslimit := ChainHandlersR32C2.op_gaslimit_chainSpecR32
  op_chainid := ChainHandlersR32C2.op_chainid_chainSpecR32
  op_selfbalance := ChainHandlersR32C5.op_selfbalance_chainSpecR32
  op_basefee := ChainHandlersR32C2.op_basefee_chainSpecR32
  op_blobhash := ChainHandlersR32C2.op_blobhash_chainSpecR32
  op_blobbasefee := ChainHandlersR32C2.op_blobbasefee_chainSpecR32
  op_slotnum := ChainHandlersR32C2.op_slotnum_chainSpecR32
  op_pop := ChainHandlersR32C2.op_pop_chainSpecR32
  op_mload := hc5.op_mload
  op_mstore := hc5.op_mstore
  op_mstore8 := hc5.op_mstore8
  op_sload := hc5.op_sload
  op_sstore := hc5.op_sstore
  op_jump := ChainHandlersR32C3.op_jump_chainSpecR32
  op_jumpi := ChainHandlersR32C3.op_jumpi_chainSpecR32
  op_pc := ChainHandlersR32C2.op_pc_chainSpecR32
  op_msize := ChainHandlersR32C2.op_msize_chainSpecR32
  op_gas := ChainHandlersR32C2.op_gas_chainSpecR32
  op_jumpdest := ChainHandlersR32C2.op_jumpdest_chainSpecR32
  op_tload := hc5.op_tload
  op_tstore := hc5.op_tstore
  op_push := hc5.op_push
  op_dup := ChainHandlersR32C2.op_dup_chainSpecR32
  op_swap := ChainHandlersR32C4.op_swap_chainSpecR32
  op_log := hc5.op_log
  op_dupn := ChainHandlersR32C2.op_dupn_chainSpecR32
  op_swapn := ChainHandlersR32C4.op_swapn_chainSpecR32
  op_exchange := ChainHandlersR32C4.op_exchange_chainSpecR32

/-! ## 3. G10-lane hop derivations (`CallSpecLiftR32` wiring) -/

/-!
The six G10 call/create-family `hop_*` fields are derived from the
`Group10CreateR32` / `Group10CallR32` A-strength handler specs via
`CallSpecLiftR32` (StrongBridgesR32.lean:576). Each derivation below takes the
G10-lane premises explicitly (the R16 callee contracts and continuation
bundle consumed by the compiled G10 specs) plus the `CallSpecLiftR32` lift
itself, so the cross-lane obligations are individually named and auditable. -/

/-- `hop_create` from the G10 lane: `Group10CreateR32.op_create_specA_r32`
lifted by `CallSpecLiftR32`. The `compute_contract_address` /
`generic_create` callee contracts are the R16-strength G10 premises. -/
theorem hop_create_of_g10
    (hlift : CallSpecLiftR32 (ofString "op_create"))
    (hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hgc : R16Shards.OpHandlersB.ChildCreateSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create")) :
    OpHandlerChainSpecR32 (ofString "op_create") :=
  hlift (R16Shards.OpHandlersB.op_create_specA_r32 hcc hgc)

/-- `hop_create2` from the G10 lane: `Group10CreateR32.op_create2_specA_r32`
lifted by `CallSpecLiftR32`. -/
theorem hop_create2_of_g10
    (hlift : CallSpecLiftR32 (ofString "op_create2"))
    (hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgc : R16Shards.OpHandlersB.ChildCreateSpecA (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create")) :
    OpHandlerChainSpecR32 (ofString "op_create2") :=
  hlift (R16Shards.OpHandlersB.op_create2_specA_r32 hU hcc2 hgc)

/-- `hop_call` from the G10 lane: `Group10CallR32.op_call_specA_r32` lifted by
`CallSpecLiftR32`. -/
theorem hop_call_of_g10
    (hlift : CallSpecLiftR32 (ofString "op_call"))
    (hWc : R16Shards.OpHandlersB.WorldAccountSpecsCall_g10)
    (hRun : R16Shards.OpHandlersB.Group10CallR32Continuations) :
    OpHandlerChainSpecR32 (ofString "op_call") :=
  hlift (R16Shards.OpHandlersB.op_call_specA_r32 hWc hRun)

/-- `hop_callcode` from the G10 lane. -/
theorem hop_callcode_of_g10
    (hlift : CallSpecLiftR32 (ofString "op_callcode"))
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hRun : R16Shards.OpHandlersB.Group10CallR32Continuations) :
    OpHandlerChainSpecR32 (ofString "op_callcode") :=
  hlift (R16Shards.OpHandlersB.op_callcode_specA_r32 hW hRun)

/-- `hop_delegatecall` from the G10 lane. -/
theorem hop_delegatecall_of_g10
    (hlift : CallSpecLiftR32 (ofString "op_delegatecall"))
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hRun : R16Shards.OpHandlersB.Group10CallR32Continuations) :
    OpHandlerChainSpecR32 (ofString "op_delegatecall") :=
  hlift (R16Shards.OpHandlersB.op_delegatecall_specA_r32 hW hRun)

/-- `hop_staticcall` from the G10 lane. -/
theorem hop_staticcall_of_g10
    (hlift : CallSpecLiftR32 (ofString "op_staticcall"))
    (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hRun : R16Shards.OpHandlersB.Group10CallR32Continuations) :
    OpHandlerChainSpecR32 (ofString "op_staticcall") :=
  hlift (R16Shards.OpHandlersB.op_staticcall_specA_r32 hW hRun)

/-! ## 4. The statement-bundle closure -/

/-- `ChainHandlersR32Stmt` with every unconditional lane closed:

* `hsetA` from `SetStorageR31.epsA_set_storage_r31` (unconditional),
* `bf`, `be`, `bx` from `ChainHandlersR31C1` (unconditional),
* `bd` from `ChainHandlersR31C1.bd_op_dispatch_r31` with the `hkgso`
  discharged by `hkgso_of_hdb hdb`,
* `hrem` from `remainingChainHandlersR32_of` (58 proved walks — 54 from
  C2/C3, three swap walks from C4, `op_selfbalance` from C5 — plus the 19
  open fields of `hc5`),
* and the open premises taken individually: the five `EvmPreservingSpecAR32`
  callee contracts (`hU`–`hgca`), the ten `hop_*` chain-WF handlers (the six
  G10 ops derivable via the `hop_*_of_g10` lemmas above, the four
  `StrongBridges`-lane ops `op_mcopy`/`op_return`/`op_revert`/
  `op_selfdestruct` derivable via the `ChainHandlersR32C5.hop_*_of_sb`
  lemmas from the lift premises `hliftMcopy`/`hliftReturn`/`hliftRevert`/
  `hliftSelfdestruct` and the `WorldAccountSpecsA` bundle `hWsd`), and the
  R32-aligned `run_frames` bound `hframes`.

Parameter types are verbatim the corresponding `ChainHandlersR32Stmt` fields,
so each future delivery plugs in with zero structural friction. -/
theorem chainHandlersR32Stmt_of
    (hdb : HdbBounded)
    (hU : EvmPreservingSpecAR32 (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "u256_to_be32"))
    (hcc : EvmPreservingSpecAR32 (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : EvmPreservingSpecAR32 (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgcr : EvmPreservingSpecAR32 (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_create"))
    (hgca : EvmPreservingSpecAR32 (fun _ => True)
      (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
      (ofString "generic_call"))
    (hliftMcopy : ChainHandlersR32C5.SBChainSpecLiftR32 (ofString "op_mcopy"))
    (hop_create : OpHandlerChainSpecR32 (ofString "op_create"))
    (hop_call : OpHandlerChainSpecR32 (ofString "op_call"))
    (hop_callcode : OpHandlerChainSpecR32 (ofString "op_callcode"))
    (hliftReturn : ChainHandlersR32C5.SBChainSpecLiftR32 (ofString "op_return"))
    (hop_delegatecall : OpHandlerChainSpecR32 (ofString "op_delegatecall"))
    (hop_create2 : OpHandlerChainSpecR32 (ofString "op_create2"))
    (hop_staticcall : OpHandlerChainSpecR32 (ofString "op_staticcall"))
    (hliftRevert : ChainHandlersR32C5.SBChainSpecLiftR32 (ofString "op_revert"))
    (hWsd : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hliftSelfdestruct : ChainHandlersR32C5.SBChainSpecLiftR32
      (ofString "op_selfdestruct"))
    (hc5 : ChainHandlersR32C5.RemainingChainHandlersR32C5)
    (hframes : TerminatingFunBoundedOn
      (fun s => EvmInvR32 s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s)
      (ofString "run_frames") K.«run_frames») :
    ChainHandlersR32Stmt where
  hsetA := epsA_set_storage_r31
  hU := hU
  hcc := hcc
  hcc2 := hcc2
  hgcr := hgcr
  hgca := hgca
  bf := ChainHandlersR31C1.bf_finish_child_r31
  be := ChainHandlersR31C1.be_frame_epilogue_r31
  bx := ChainHandlersR31C1.bx_frame_exception_r31
  bd := ChainHandlersR31C1.bd_op_dispatch_r31 (hkgso_of_hdb hdb)
  hop_mcopy := ChainHandlersR32C5.hop_mcopy_of_sb hliftMcopy
  hop_create := hop_create
  hop_call := hop_call
  hop_callcode := hop_callcode
  hop_return := ChainHandlersR32C5.hop_return_of_sb hliftReturn
  hop_delegatecall := hop_delegatecall
  hop_create2 := hop_create2
  hop_staticcall := hop_staticcall
  hop_revert := ChainHandlersR32C5.hop_revert_of_sb hliftRevert
  hop_selfdestruct := ChainHandlersR32C5.hop_selfdestruct_of_sb hWsd hliftSelfdestruct
  hrem := remainingChainHandlersR32_of hc5
  hframes := hframes

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C
