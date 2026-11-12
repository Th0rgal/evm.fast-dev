import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C4

/-! # Wave 8 R32 C5: hop walks from `StrongBridges` A-specs + `op_selfbalance`

This shard advances the `RemainingChainHandlersR32C4` tail:

* **Four hop walks** (`hop_mcopy_of_sb`, `hop_return_of_sb`, `hop_revert_of_sb`,
  `hop_selfdestruct_of_sb`): the R16-era `StrongBridges` shard carries
  unconditional A-strength chain-handler specs for `op_mcopy`, `op_return`,
  `op_revert` (`StrongBridges.op_mcopy_chainSpecA` etc.) and a
  `WorldAccountSpecsA`-parameterised one for `op_selfdestruct`
  (`StrongBridges.op_selfdestruct_chainSpecA`). Deriving the R32 chain-handler
  statements from them needs a single named lift premise per op
  (`SBChainSpecLiftR32`, mirroring `StrongBridgesR32.CallSpecLiftR32` for the
  G10 lane): the lift strengthens the entry guard from `EvmInv` to
  `EvmInvR32 ∧ HeadMemChainWF ∧ ¬ EvmDone` and aligns the post to the R32
  chain shape. Keeping the lift as an explicit premise is honest — the
  R32 entry guard is strictly stronger, so the A-spec applies on entry, but
  the R32 post additionally carries the `WitnessDbOK`/system-address
  obligations of `EvmInvR32`, which the R16 A-spec does not provide by
  itself.
* **`op_selfbalance`** (`op_selfbalance_chainSpecR32`): proved unconditionally
  with the `HandlerRunA32` combinator framework — `charge_gas 5`, then
  `get_account` on the callee address loaded from the head frame (`C3`
  `epsA32_get_account`), `stack_push` of the four-word balance slot, `pc_add`,
  return. Every callee has an unconditional `EvmPreservingSpecA32` leaf, so
  the walk needs no premises.
* **`RemainingChainHandlersR32C5`**: the 19 fields of the C4 tail that remain
  open (`op_selfbalance` closed here), so the assembly
  (`ChainHandlersR32C`) consumes them individually.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C5

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8Contracts.M23
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.ContractParts
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C1
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C2
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C3
open InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C4

/-! ## 1. The `StrongBridges` A-spec lift premise -/

/-- Lift obligation for the `StrongBridges` lane (mirroring
`StrongBridgesR32.CallSpecLiftR32` for the G10 lane): transport the R16-era
`StrongBridges.OpHandlerChainSpecA` statement to the R32 chain-handler
statement. The R32 entry guard (`EvmInvR32 ∧ HeadMemChainWF ∧ ¬ EvmDone`) is
strictly stronger than the R16 entry guard, so the A-spec applies on entry;
the R32 post, however, carries the `WitnessDbOK` and system-address
obligations of `EvmInvR32`, which the lift must re-establish on the exit
state. Kept as an explicit, individually named premise. -/
def SBChainSpecLiftR32 (fname : MlS) : Prop :=
  StrongBridges.OpHandlerChainSpecA fname → OpHandlerChainSpecR32 fname

/-! ## 2. The four hop walks -/

/-- `hop_mcopy` from the `StrongBridges` lane:
`StrongBridges.op_mcopy_chainSpecA` (unconditional A-strength spec) lifted by
`SBChainSpecLiftR32`. -/
theorem hop_mcopy_of_sb (hlift : SBChainSpecLiftR32 (ofString "op_mcopy")) :
    OpHandlerChainSpecR32 (ofString "op_mcopy") :=
  hlift StrongBridges.op_mcopy_chainSpecA

/-- `hop_return` from the `StrongBridges` lane. -/
theorem hop_return_of_sb (hlift : SBChainSpecLiftR32 (ofString "op_return")) :
    OpHandlerChainSpecR32 (ofString "op_return") :=
  hlift StrongBridges.op_return_chainSpecA

/-- `hop_revert` from the `StrongBridges` lane. -/
theorem hop_revert_of_sb (hlift : SBChainSpecLiftR32 (ofString "op_revert")) :
    OpHandlerChainSpecR32 (ofString "op_revert") :=
  hlift StrongBridges.op_revert_chainSpecA

/-- `hop_selfdestruct` from the `StrongBridges` lane: the A-strength spec is
parameterised on the `WorldAccountSpecsA` world bundle (same premise shape as
the G10 `hop_callcode_of_g10` lane). -/
theorem hop_selfdestruct_of_sb (hW : R16Shards.OpHandlersB.WorldAccountSpecsA)
    (hlift : SBChainSpecLiftR32 (ofString "op_selfdestruct")) :
    OpHandlerChainSpecR32 (ofString "op_selfdestruct") :=
  hlift (StrongBridges.op_selfdestruct_chainSpecA hW)

/-! ## 3. `op_selfbalance` -/

theorem op_selfbalance_chainSpecR32 : OpHandlerChainSpecR32 (ofString "op_selfbalance") := by
  refine opHandlerChainSpecR32_of_run 549 (by rw [guestAst_len]; decide)
    Guest.Software.guestFn_op_selfbalance rfl ?_
  intro F s0 _ _ _
  dsimp only [Guest.Software.guestFn_op_selfbalance, extractFn,
    InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.expListToHOLStructural,
    InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural,
    Option.map, List.map]
  refine HandlerRunA32.seq_charge_gas_exact (Q := fun _ => True) ?_ ?_ ?_
  · intro t w hv _ _ _
    simp only [evalHOLExact] at hv
    injection hv with h1
    injection h1 with h2
    injection h2 with h3
    subst h3
    decide
  · intro t cpost amtw _ _ _ _ _ _ _ _ _ _
    trivial
  · exact HandlerRunA32.decCall_simple epsA32_get_account
      (HandlerRunA32.seq_call_simple epsA32_stack_push
        (HandlerRunA32.seq_call_simple epsA32_pc_add (HandlerRunA32.ret _)))

/-! ## 4. The remaining bundle -/

/-- The 19 still-open fields of the C4 tail (`op_selfbalance` closed
unconditionally by `op_selfbalance_chainSpecR32` above). -/
structure RemainingChainHandlersR32C5 : Prop where
  op_keccak : OpHandlerChainSpecR32 (ofString "op_keccak")
  op_balance : OpHandlerChainSpecR32 (ofString "op_balance")
  op_calldataload : OpHandlerChainSpecR32 (ofString "op_calldataload")
  op_calldatacopy : OpHandlerChainSpecR32 (ofString "op_calldatacopy")
  op_codecopy : OpHandlerChainSpecR32 (ofString "op_codecopy")
  op_extcodesize : OpHandlerChainSpecR32 (ofString "op_extcodesize")
  op_extcodecopy : OpHandlerChainSpecR32 (ofString "op_extcodecopy")
  op_returndatacopy : OpHandlerChainSpecR32 (ofString "op_returndatacopy")
  op_extcodehash : OpHandlerChainSpecR32 (ofString "op_extcodehash")
  op_blockhash : OpHandlerChainSpecR32 (ofString "op_blockhash")
  op_mload : OpHandlerChainSpecR32 (ofString "op_mload")
  op_mstore : OpHandlerChainSpecR32 (ofString "op_mstore")
  op_mstore8 : OpHandlerChainSpecR32 (ofString "op_mstore8")
  op_sload : OpHandlerChainSpecR32 (ofString "op_sload")
  op_sstore : OpHandlerChainSpecR32 (ofString "op_sstore")
  op_tload : OpHandlerChainSpecR32 (ofString "op_tload")
  op_tstore : OpHandlerChainSpecR32 (ofString "op_tstore")
  op_push : OpPushBoundedChainSpecR32
  op_log : OpLogBoundedChainSpecR32

/-- The C4 tail bundle, derived from the C5 tail (`op_selfbalance` closed). -/
theorem remainingChainHandlersR32C4_of_c5 (hc5 : RemainingChainHandlersR32C5) :
    ChainHandlersR32C4.RemainingChainHandlersR32C4 where
  op_keccak := hc5.op_keccak
  op_balance := hc5.op_balance
  op_calldataload := hc5.op_calldataload
  op_calldatacopy := hc5.op_calldatacopy
  op_codecopy := hc5.op_codecopy
  op_extcodesize := hc5.op_extcodesize
  op_extcodecopy := hc5.op_extcodecopy
  op_returndatacopy := hc5.op_returndatacopy
  op_extcodehash := hc5.op_extcodehash
  op_blockhash := hc5.op_blockhash
  op_selfbalance := op_selfbalance_chainSpecR32
  op_mload := hc5.op_mload
  op_mstore := hc5.op_mstore
  op_mstore8 := hc5.op_mstore8
  op_sload := hc5.op_sload
  op_sstore := hc5.op_sstore
  op_tload := hc5.op_tload
  op_tstore := hc5.op_tstore
  op_push := hc5.op_push
  op_log := hc5.op_log

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR32C5
