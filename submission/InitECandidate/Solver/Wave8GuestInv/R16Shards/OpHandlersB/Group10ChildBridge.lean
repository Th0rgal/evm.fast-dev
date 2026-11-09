import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreates
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail2
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail3
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail4
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail5

/-! # Group 10 child bridge: the conditional 7-bundle of call/create handler specs

This file assembles the seven `Group10CallsCreates`-family handler specs proved across
`Group10CallsCreates.lean` and its tails (`Tail2`-`Tail5`) into a single conjunction,
conditional only on the shared world-account and callee-contract hypotheses:

* `op_create`      (guest AST index 599, `Group10CallsCreates.lean`),
* `op_call`        (guest AST index 603, `Group10CallsCreatesTail4.lean`),
* `op_callcode`    (guest AST index 604, `Group10CallsCreatesTail3.lean`),
* `op_delegatecall`(guest AST index 605, `Group10CallsCreatesTail5.lean`),
* `op_create2`     (guest AST index 600, `Group10CallsCreates.lean`),
* `op_staticcall`  (guest AST index 606, `Group10CallsCreatesTail2.lean`),
* `op_selfdestruct`(guest AST index 570, `Group10CallsCreates.lean`).

Every leaf is an `OpHandlerSpecA`: the aligned handler contract whose precondition carries
`Group10.HeadMemChainWF` alongside `EvmInv`/`¬EvmDone`, and whose postcondition is
`OpDispatchPostA`.  This is exactly the leaf shape consumed by the aligned dispatch regime
(`HeadMemBridge.OpDispatchSpecA` / `gbody_run_frames_aligned` in
`HeadMemAlignedBridge.lean`), so this bundle is the Group 10 contribution to that assembly.

The bundle stays *conditional* by design:

* `EvmRun` alone does not imply `Group10.HeadMemChainWF` (the chain-wide invariant needs
  entry establishment, cf. `HeadMemAlignedBridge.lean`), so the leaves cannot be weakened
  to the unaligned `R11Shards.OpDispatchSpec.OpHandlerSpec` here; the postcondition half of
  that conversion is `opDispatchPostA_to_standard`, to be applied once the aligned
  dispatch spec is assembled at top level.
* the world-account record `WorldAccountSpecsA` / `WorldAccountSpecsCall_g10` and the
  callee contracts for `generic_call`, `generic_create`, `compute_contract_address`,
  `compute_create2_contract_address`, and `u256_to_be32` are not yet proved
  unconditionally anywhere; they remain hypotheses for the top-level instantiation.

`op_call` needs the strengthened world record `WorldAccountSpecsCall_g10`
(`WorldAccountSpecsA` plus the `ev+32` keep-word through `is_account_alive`); the plain
record for the other six leaves is recovered by the structure projection. -/

set_option Elab.async false
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.GuestGlobalKeep
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16Shards (evmInvAt_of_htab_step evaluate_be_eq)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.StateRestoreEpilogue (noCatchableRaise evaluate_noCatchableRaise)
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlers
open InitECandidate.Solver.Wave8Contracts.M23

/-- The conditional 7-bundle of Group 10 call/create handler specs, in the relative leaf
order of `RemainingOpHandlersBSpec`.  Given the world-account record (strengthened with
the `op_call` keep-word), the `generic_call`/`generic_create` callee contracts, the two
contract-address derivations, and `u256_to_be32`, all seven aligned handler specs hold. -/
theorem group10_child_bridge_g10
    (hWc : WorldAccountSpecsCall_g10)
    (hcc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_contract_address"))
    (hcc2 : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "compute_create2_contract_address"))
    (hgc : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_create"))
    (hgcl : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "generic_call"))
    (hU : EvmPreservingSpecA (fun _ => True) (fun s _ post => LocFrame s post)
      (ofString "u256_to_be32")) :
    OpHandlerSpecA (ofString "op_create") ∧
    OpHandlerSpecA (ofString "op_call") ∧
    OpHandlerSpecA (ofString "op_callcode") ∧
    OpHandlerSpecA (ofString "op_delegatecall") ∧
    OpHandlerSpecA (ofString "op_create2") ∧
    OpHandlerSpecA (ofString "op_staticcall") ∧
    OpHandlerSpecA (ofString "op_selfdestruct") := by
  have hW : WorldAccountSpecsA := hWc.toWorldAccountSpecsA
  exact ⟨op_create_specA_g10 hW hcc hgc,
    op_call_specA_g10 hWc hgcl,
    op_callcode_specA_g10 hW hgcl,
    op_delegatecall_specA_g10 hW hgcl,
    op_create2_specA_g10 hU hW hcc2 hgc,
    op_staticcall_specA_g10 hW hgcl,
    op_selfdestruct_specA hW⟩

end InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
