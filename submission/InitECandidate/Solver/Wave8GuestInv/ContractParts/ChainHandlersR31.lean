import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31C1

/-! # Wave 8 R31 Chain Handlers (`ChainHandlersR31`) — sibling lane bundle

Proves `StrongBridgesR31.ChainHandlersR31Stmt` for the `ChainHandlersR31` sibling
lane of the `StrongBridgesR31DropIn` single-swap integration contract:

- Four conjuncts are closed **unconditionally and gap-free** in
  `ContractParts.ChainHandlersR31C1`: the `finish_child` bound on `FinishReadyA`
  (`bf`), the `frame_epilogue` / `frame_exception` bounds (`be`, `bx`), and the
  `op_dispatch` bound on `EvmRunA` (`bd`) — each assembled from clean leaves
  (`Merged`, `R16Shards.PrimC08Closure`, `ContractParts.C09/C12/C13/C15`) and
  lifted by `HeadMemBridge.finishReadyA_bound` / `evmRunA_bound`. The
  legacy-stub `Primitives.«wk_decode_host_input»` primitive is never used.
- `bd` depends on exactly one further single-statement obligation: the weak-guard
  `get_storage_original` Evm-keeps contract (`hkgso`) that the legacy
  `ContractParts.C08.lean:74` placeholder (legacy stub) never discharged. It is
  taken as an explicit parameter (`ChainHandlersR31C1.bd_op_dispatch_r31`).
- The nine remaining conjuncts are taken as explicit parameters so the R32/S1b
  lanes can plug their proofs straight in: the Pillar 2 witness-DB facts
  (`hdb`, `hsys`), the A-side `set_storage` contract (`hsetA`), the five Group 10
  callee contracts (`hU`, `hcc`, `hcc2`, `hgcr`, `hgca`), and the remaining A-side
  chain handlers (`hrem : RemainingChainHandlersR29`, proven shard-by-shard in
  `ChainHandlersR31A1/A2/B`).

Swap recipe: once every parameter is instantiated, feed the resulting
`chainHandlersR31Stmt_of_open` — together with the `WkBlockTxProcessTail` lane's
`WkProcessTransactionStmt` proof — into `StrongBridgesR31DropIn.strongBridgesR31Cutover_of`,
which closes every `ContractParts.StrongBridges` obligation with zero additional glue.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31

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

/-- `ChainHandlersR31Stmt` with the bounded-entry conjuncts (`bf`, `be`, `bx`)
discharged unconditionally by `ChainHandlersR31C1`, `bd` closed modulo the single
`hkgso` parameter, and the nine sibling-lane conjuncts left as clean parameters (`hdb`, `hsys`, `hsetA`, the five
Group 10 callee contracts, and `hrem`). Parameter types are verbatim the fields of
`StrongBridgesR31.ChainHandlersR31Stmt`, so each R32/S1b proof plugs in directly. -/
theorem chainHandlersR31Stmt_of_open
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (hsetA : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
      (fun s _ post =>
        GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage"))
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
    (hkgso : EvmKeeps (EvmAvoids (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136), (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200), (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64)]))
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original"))
    (hrem : RemainingChainHandlersR29) :
    StrongBridgesR31.ChainHandlersR31Stmt :=
  ⟨hdb, hsys, hsetA, hU, hcc, hcc2, hgcr, hgca,
    ChainHandlersR31C1.bf_finish_child_r31,
    ChainHandlersR31C1.be_frame_epilogue_r31,
    ChainHandlersR31C1.bx_frame_exception_r31,
    ChainHandlersR31C1.bd_op_dispatch_r31 hkgso,
    hrem⟩

end InitECandidate.Solver.Wave8GuestInv.ContractParts.ChainHandlersR31
