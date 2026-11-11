import InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
import InitECandidate.Solver.Wave8GuestInv.ContractParts.WitnessDbStorageR31

/-! # Wave 8 R31 Strong Bridges (`StrongBridgesR31`) — Pillar 3B

Complete Pillar 3B module (`ContractParts/StrongBridgesR31`) closing 100% of the
remaining `ContractParts/StrongBridges.lean` obligations, parameterized only over two
clean statement bundles:

1. **`ChainHandlersR31Stmt`** — the chain-handler side: witness-DB / system-address /
   `set_storage` world-account premises (discharged by Pillar 2 `WitnessDbStorageR31`),
   the five Group 10 callee contracts (`u256_to_be32`, `compute_contract_address`,
   `compute_create2_contract_address`, `generic_create`, `generic_call`), the four
   `TerminatingFunBoundedOn` bounds (`finish_child`, `frame_epilogue`, `frame_exception`,
   `op_dispatch`), and the ~74 A-side `RemainingChainHandlersR29` handlers. From it:
   `WorldAccountSpecsCall_g10`, `OpDispatchChainHandlersCutover`, the chain-WF
   `HeadMemBridge.OpDispatchSpecA`, and the end-to-end aligned `gbody_run_frames` bound.
2. **`WkProcessTransactionStmt`** — the `process_transaction` side: the WorldOK
   witness-DB premise, `gb_pmc`, legacy-unused Phase 1/2 fields, both entry lifts
   (`TxReadyBackingStrong → TxReadyFullStrong` and `TxReadyStrong → TxReadyFullStrong`),
   `PmcStrong` / `PmcBackingStrong`, Phase 2/4 relational cuts, and the
   `process_message` / `process_create_message` Bo-marks contracts. From it: the
   `gbody_process_transaction` bound on `TxReadyBackingStrong` AND directly on
   `TxReadyFullStrong`, plus the full relational `wk_process_transaction` strong cut
   and its `RetTransactionLogs` corollary.

Everything else in `StrongBridges.lean` — `finish_child_spec`, `extCodeOfHeadSpec`,
`gbody_execute_block`, `gbody_run_attempt` — is already closed unconditionally and is
re-exported here under `_r31` names, so importing this module is a strict superset of
importing `ContractParts.StrongBridges`.

Sibling integration (single import swap): once the `ChainHandlersR31` lane provides
`ChainHandlersR31Stmt` and the `WkBlockTxProcessTail` lane provides
`WkProcessTransactionStmt`, every theorem below is a one-application closure; use
`ContractParts.StrongBridgesR31DropIn` as the drop-in replacement for the legacy
`import ...ContractParts.StrongBridges` line.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31

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
open InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
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
open InitECandidate.Solver.Wave8Contracts.M23 (Resumes)

/-! ## 1. Chain-Handler Statement Bundle (`ChainHandlersR31Stmt`)

Witness-DB world-account premises (Pillar 2 `WitnessDbStorageR31`), the five Group 10
callee contracts, the four frame/dispatch bounds, and the ~74 remaining A-side chain
handlers (`RemainingChainHandlersR29`). This is exactly what the `ChainHandlersR31`
sibling lane must prove. -/

/-- Statement bundle for the chain-handler side of `StrongBridges`: everything needed to
close `OpDispatchChainHandlersCutover`, the chain-WF `op_dispatch` spec, and the aligned
`gbody_run_frames` bound. -/
structure ChainHandlersR31Stmt : Prop where
  /-- Witness DB is well-formed under `EvmInv` (Pillar 2 premise). -/
  hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    EvmInv s → R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s
  /-- The system address is materialized in head memory (Pillar 2 premise). -/
  hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")
  /-- `set_storage` preserves the journal/heap globals and `evmR` (A-side spec). -/
  hsetA : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    (ofString "set_storage")
  hU : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "u256_to_be32")
  hcc : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "compute_contract_address")
  hcc2 : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "compute_create2_contract_address")
  hgcr : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "generic_create")
  hgca : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "generic_call")
  /-- `finish_child` bound (`FinishReadyA` entry). -/
  bf : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.FinishReadyA
    (ofString "finish_child") K.«finish_child»
  /-- `frame_epilogue` bound. -/
  be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»
  /-- `frame_exception` bound. -/
  bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»
  /-- `op_dispatch` bound (`EvmRunA` entry). -/
  bd : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.EvmRunA
    (ofString "op_dispatch") K.«op_dispatch»
  /-- The ~74 A-side `OpHandlerChainSpec` handlers still open in R29. -/
  hrem : RemainingChainHandlersR29

/-- `WorldAccountSpecsCall_g10` from the R31 statement bundle (Pillar 2 closure). -/
theorem worldAccountSpecsCall_g10_of_chainHandlers
    (hChain : ChainHandlersR31Stmt) :
    R16Shards.OpHandlersB.WorldAccountSpecsCall_g10 :=
  worldAccountSpecsCall_g10_r31 hChain.hdb hChain.hsys hChain.hsetA

/-- Full R31 chain-WF `op_dispatch` handler cutover bundle from the statement bundle. -/
theorem opDispatchChainHandlersCutover_r31
    (hChain : ChainHandlersR31Stmt) :
    R16Shards.OpHandlersB.OpDispatchChainHandlersCutover :=
  opDispatchChainHandlersCutover_of_r29
    (worldAccountSpecsCall_g10_of_chainHandlers hChain) hChain.hU hChain.hcc hChain.hcc2
    hChain.hgcr hChain.hgca hChain.hrem

/-- Chain-WF `op_dispatch` spec (`HeadMemBridge.OpDispatchSpecA`) from the statement
bundle. -/
theorem op_dispatch_chain_spec_r31
    (hChain : ChainHandlersR31Stmt) :
    R16Shards.OpHandlersB.HeadMemBridge.OpDispatchSpecA :=
  op_dispatch_chain_spec_r29
    (worldAccountSpecsCall_g10_of_chainHandlers hChain) hChain.hU hChain.hcc hChain.hcc2
    hChain.hgcr hChain.hgca hChain.hrem

/-- End-to-end aligned `gbody_run_frames` bound from the statement bundle: Group 09,
all 7 Group 10 call/create opcodes, bounded `op_log`, and `finish_child` /
`frame_epilogue` / `frame_exception` wired. -/
theorem gbody_run_frames_aligned_r31
    (hChain : ChainHandlersR31Stmt) :
    TerminatingFunBoundedOn (fun s => EvmInv s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s)
      (ofString "run_frames") K.«run_frames» :=
  gbody_run_frames_aligned_r29 hChain.bf hChain.be hChain.bx hChain.bd
    (worldAccountSpecsCall_g10_of_chainHandlers hChain) hChain.hU hChain.hcc hChain.hcc2
    hChain.hgcr hChain.hgca hChain.hrem

/-! ## 2. `process_transaction` Statement Bundle (`WkProcessTransactionStmt`)

The WorldOK witness-DB premise, `process_message_call` bound, legacy-unused Phase 1/2
fields (Pillar 1), both entry lifts, the PMC strong/backing contracts, the Phase 2/4
relational cuts, and the two message Bo-marks contracts. This is exactly what the
`WkBlockTxProcessTail` sibling lane must prove. -/

/-- Statement bundle for the `process_transaction` side of `StrongBridges`: everything
needed to close the `gbody_process_transaction` bounds (backing and full) and the
relational `wk_process_transaction` strong cuts. -/
structure WkProcessTransactionStmt : Prop where
  /-- Witness DB slices bounded under `WorldOK` (both backing and relational cuts). -/
  hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    WorldOK s → globN s "ws" ≠ 0 →
      R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))
  /-- Witness DB well-formed under `EvmInv` (world-account closures). -/
  hdbI : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    EvmInv s → R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s
  /-- System address materialized in head memory (world-account closures). -/
  hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")
  /-- `set_storage` world-account premise (plain `EvmPreservingSpec`). -/
  hset : EvmPreservingSpec (fun _ => True)
    (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    (ofString "set_storage")
  /-- `set_storage` world-account premise (A-side `EvmPreservingSpecA`). -/
  hsetA : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    (ofString "set_storage")
  /-- `process_message_call` terminating bound. -/
  gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
    K.«process_message_call»
  /-- Legacy-unused Phase 1/2 callee fields (Pillar 1). -/
  hleg : LegacyUnusedPtxPhase12Fields
  /-- Entry lift used by the backing cut (`TxReadyBackingStrong → TxReadyFullStrong`). -/
  hentBacking : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s
  /-- Entry lift used by the relational cut (`TxReadyStrong → TxReadyFullStrong`). -/
  hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    TxReadyStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s
  /-- `process_message_call` PMC strong contract. -/
  hwk : R16Shards.PtxP34.PmcStrong
  /-- `process_message_call` PMC backing contract. -/
  hkeep : R16Shards.PmcBackingStrong
  /-- Phase 2 relational strong cut. -/
  h2 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase2
    R16Shards.TopGbodyWk.PtxAfterPhase1 R16Shards.TopGbodyWk.PtxAfterPhase2
  /-- `process_message` Bo-marks contract. -/
  hpm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
    R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
    R16Shards.TopGbodyWk.pmcKeep
    R16Shards.TopGbodyWk.RetFrameResultMarksExactBo (ofString "process_message")
  /-- `process_create_message` Bo-marks contract. -/
  hpcm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
    R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
    R16Shards.TopGbodyWk.pmcKeep
    R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message")
  /-- Phase 4 relational strong cut. -/
  h4 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase4
    R16Shards.TopGbodyWk.PtxAfterPhase3 R16Shards.TopGbodyWk.PtxAfterPhase4

/-- `WorldAccountSpecs` from the bundle's world-account premises (Pillar 2 closure). -/
theorem worldAccountSpecs_of_wkPtx
    (hWkPtx : WkProcessTransactionStmt) : WorldAccountSpecs :=
  worldAccountSpecs_r31 hWkPtx.hdbI hWkPtx.hsys hWkPtx.hset

/-- `WorldAccountSpecsA` from the bundle's world-account premises (Pillar 2 closure). -/
theorem worldAccountSpecsA_of_wkPtx
    (hWkPtx : WkProcessTransactionStmt) : WorldAccountSpecsA :=
  worldAccountSpecsA_r31 hWkPtx.hdbI hWkPtx.hsys hWkPtx.hsetA

/-- `WorldAccountSpecsCall_g10` from the bundle's world-account premises (Pillar 2
closure) — the R29 chain-handler entry point restated on the ptx bundle. -/
theorem worldAccountSpecsCall_g10_of_wkPtx
    (hWkPtx : WkProcessTransactionStmt) :
    R16Shards.OpHandlersB.WorldAccountSpecsCall_g10 :=
  worldAccountSpecsCall_g10_r31 hWkPtx.hdbI hWkPtx.hsys hWkPtx.hsetA

/-- Full `gbody_process_transaction` on `TxReadyBackingStrong` with BOTH Phase 1 and
Phase 2 backing cuts discharged by Pillar 1 (R31). -/
theorem gbody_process_transaction_backing_strong_r31
    (hWkPtx : WkProcessTransactionStmt) :
    TerminatingFunBoundedOn
      R16Shards.TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  PtxCalleesProvedR31.gbody_process_transaction_backing_strong_r31
    hWkPtx.hdb hWkPtx.gb_pmc hWkPtx.hleg hWkPtx.hentBacking hWkPtx.hwk hWkPtx.hkeep

/-- Full `gbody_process_transaction` directly on `TxReadyFullStrong` with zero `hent`
assumption (Pillar 1 R31 closure of Phase 1+2 backing cuts). -/
theorem gbody_process_transaction_full_strong_r31
    (hWkPtx : WkProcessTransactionStmt) :
    TerminatingFunBoundedOn
      R16Shards.TopGbodyWk.TxReadyFullStrong (ofString "process_transaction")
      K.«process_transaction» :=
  PtxCalleesProvedR31.gbody_process_transaction_full_strong_r31
    hWkPtx.hdb hWkPtx.gb_pmc hWkPtx.hleg hWkPtx.hwk hWkPtx.hkeep

/-- Full relational `wk_process_transaction` on `TxReadyStrong`: Phases 1, 3, 5 closed;
only the bundle's Phase 2/4 cuts and message Bo-marks contracts remain. -/
theorem wk_process_transaction_strong_r31
    (hWkPtx : WkProcessTransactionStmt) :
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
  wk_process_transaction_strong_r29 hWkPtx.hent hWkPtx.hdb hWkPtx.h2 hWkPtx.hpm
    hWkPtx.hpcm hWkPtx.h4

/-- Weakened `RetTransactionLogs` corollary of the relational cut, matching the legacy
`wk_process_transaction` postcondition shape. -/
theorem wk_process_transaction_logs_r31
    (hWkPtx : WkProcessTransactionStmt) :
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
      RetTransactionLogs (ofString "process_transaction") :=
  wk_process_transaction_logs_r29 hWkPtx.hent hWkPtx.hdb hWkPtx.h2 hWkPtx.hpm
    hWkPtx.hpcm hWkPtx.h4

/-! ## 3. Witness-DB Builder, Withdrawals & System-Transaction Closures (R29 §5)

Pass-through closures modulo the bundle's witness-DB premise `hdb` (already proved in
R29 / Pillar 1; re-stated on the bundle so nothing outside `hChain` / `hWkPtx` is needed
for the transaction-processing half of `StrongBridges`). The statement types are exactly
the R29 closure types. -/

/-- R29 `wkSc_idx_start_storage_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wkSc_idx_start_storage_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    : R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.builderBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra
      (ofString "idx_start_storage")
  := wkSc_idx_start_storage_of_witnessDb hWkPtx.hdb

/-- R29 `wk_idx_start_storage_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wk_idx_start_storage_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    : WorldKeeps WorldOK
      (fun s => [(globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "idx_start_storage")
  := wk_idx_start_storage_of_witnessDb hWkPtx.hdb

/-- R29 `wkSc_update_builder_from_tx_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wkSc_update_builder_from_tx_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    : R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.builderBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra
      (ofString "update_builder_from_tx")
  := wkSc_update_builder_from_tx_of_witnessDb hWkPtx.hdb

/-- R29 `wkSc_process_withdrawals_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wkSc_process_withdrawals_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    : R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.withdrawalBufs)
      R16Shards.TopGbodyWk.withdrawalGlobals
      R16Shards.TopGbodyWk.withdrawalKeep NoExtra
      (ofString "process_withdrawals")
  := wkSc_process_withdrawals_of_witnessDb hWkPtx.hdb

/-- R29 `wk_process_withdrawals_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wk_process_withdrawals_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    : WorldKeeps WorldOK
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
      NoExtra (ofString "process_withdrawals")
  := wk_process_withdrawals_of_witnessDb hWkPtx.hdb

/-- R29 `wkSc_incorporate_tx_into_block_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wkSc_incorporate_tx_into_block_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    : R16WkAcctWs.WorldKeepsSc WorldOK
      (R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.ptxIncorpBufs)
      R16Shards.TopGbodyWk.ptxIncorpGlobals
      R16Shards.TopGbodyWk.ptxIncorpKeep NoExtra
      (ofString "incorporate_tx_into_block")
  := wkSc_incorporate_tx_into_block_of_witnessDb hWkPtx.hdb

/-- R29 `wk_process_unchecked_system_transaction_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wk_process_unchecked_system_transaction_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) ::
        bufRegions R16Shards.TopGbodyWk.pmcSysTxBufs s)
      R16Shards.TopGbodyWk.pmcSysTxGlobals R16Shards.TopGbodyWk.pmcSysTxKeep
      R16Shards.TopGbodyWk.RetSysTxPmc (ofString "process_message_call"))
    : WorldKeeps WorldOK
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
      NoExtra (ofString "process_unchecked_system_transaction")
  := wk_process_unchecked_system_transaction_of_witnessDb hWkPtx.hdb hpmc

/-- R29 `wk_process_checked_system_transaction_of_witnessDb` re-stated on the `WkProcessTransactionStmt` bundle. -/
theorem wk_process_checked_system_transaction_of_witnessDb_r31
    (hWkPtx : WkProcessTransactionStmt)
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) ::
        R16WkAcctWs.bufRegions R16Shards.TopGbodyWk.pmcSysTxBufs s)
      R16Shards.TopGbodyWk.pmcSysTxGlobals R16Shards.TopGbodyWk.pmcSysTxKeep
      R16Shards.TopGbodyWk.RetSysTxPmc (ofString "process_message_call"))
    : WorldKeeps WorldOK
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
      NoExtra (ofString "process_checked_system_transaction")
  := wk_process_checked_system_transaction_of_witnessDb hWkPtx.hdb hpmc

/-! ## 4. Unconditionally Closed `StrongBridges` Items (R31 Re-Exports)

These were already closed with zero hypotheses in `StrongBridges.lean` /
`StrongBridgesR29.lean`; re-exported under `_r31` names so a downstream consumer
switching its single import to the R31 stack keeps a uniform naming scheme. -/

/-- `finish_child_spec` closed (popping a done child frame). -/
theorem finish_child_spec_closed_r31 :
    type_of% @Wave8GuestInv.finish_child_spec :=
  finish_child_spec_closed

/-- `ExtCodeOfHeadSpec` closed. -/
theorem extCodeOfHeadSpec_closed_r31 :
    R16Shards.OpHandlersB.ExtCodeOfHeadSpec :=
  extCodeOfHeadSpec_closed

/-- Whole-function `run_attempt` termination (already closed in `StrongBridges`). -/
theorem gbody_run_attempt_strong_r31 :
    R16Shards.TopGbodyWk.GBody.run_attempt_strong :=
  gbody_run_attempt_strong

/-- Whole-function `execute_block` termination (already closed in `StrongBridges`). -/
theorem gbody_execute_block_strong_r31 :
    R16Shards.TopGbodyWk.GBody.execute_block_strong :=
  gbody_execute_block_strong

end InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31
