import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31

/-! # Wave 8 R31 Drop-In Wrapper (`StrongBridgesR31DropIn`)

Drop-in replacement for the legacy `import ...ContractParts.StrongBridges` line:
importing this module provides every name the legacy import provided (all of
`ContractParts.StrongBridges` is still transitively imported and opened downstream),
plus the R31 closures.

Single-swap integration contract:
- The `ChainHandlersR31` sibling lane proves `StrongBridgesR31.ChainHandlersR31Stmt`.
- The `WkBlockTxProcessTail` sibling lane proves `StrongBridgesR31.WkProcessTransactionStmt`.
- Applying `strongBridgesR31Cutover_of` to those two proofs then yields every
  `StrongBridges` obligation — the closed ones (`finish_child_spec`,
  `extCodeOfHeadSpec`, `gbody_execute_block`, `gbody_run_attempt`) and the two
  parameterized halves (chain handlers / `run_frames`, and `process_transaction`) —
  in one structure, with zero additional glue.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31DropIn

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
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

/-- Everything the legacy `ContractParts.StrongBridges` import owed, with the R31
statement bundles as the only parameters: the four unconditionally closed items,
the chain-handler half (`op_dispatch` cutover + aligned `gbody_run_frames`), and the
`process_transaction` half (backing/full bounds + relational strong cut and its
`RetTransactionLogs` corollary). -/
structure StrongBridgesR31Cutover : Prop where
  /-- `finish_child_spec` closed (popping a done child frame). -/
  finish_child_spec : type_of% @Wave8GuestInv.finish_child_spec
  /-- `ExtCodeOfHeadSpec` closed. -/
  ext_code_of_head : R16Shards.OpHandlersB.ExtCodeOfHeadSpec
  /-- Chain-WF `op_dispatch` spec. -/
  op_dispatch_chain_spec : R16Shards.OpHandlersB.HeadMemBridge.OpDispatchSpecA
  /-- Full chain-WF `op_dispatch` handler cutover bundle. -/
  chain_handlers_cutover : R16Shards.OpHandlersB.OpDispatchChainHandlersCutover
  /-- End-to-end aligned `gbody_run_frames` bound. -/
  gbody_run_frames : TerminatingFunBoundedOn
    (fun s => EvmInv s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s)
    (ofString "run_frames") K.«run_frames»
  /-- `gbody_process_transaction` bound on `TxReadyBackingStrong`. -/
  gbody_process_transaction_backing : TerminatingFunBoundedOn
    R16Shards.TxReadyBackingStrong (ofString "process_transaction")
    K.«process_transaction»
  /-- `gbody_process_transaction` bound directly on `TxReadyFullStrong`. -/
  gbody_process_transaction_full : TerminatingFunBoundedOn
    R16Shards.TopGbodyWk.TxReadyFullStrong (ofString "process_transaction")
    K.«process_transaction»
  /-- Full relational `wk_process_transaction` strong cut on `TxReadyStrong`. -/
  wk_process_transaction_strong : WorldKeeps TxReadyStrong
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
      (ofString "process_transaction")
  /-- Weakened `RetTransactionLogs` corollary (legacy postcondition shape). -/
  wk_process_transaction_logs : WorldKeeps TxReadyStrong
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
      RetTransactionLogs (ofString "process_transaction")
  /-- Whole-function `execute_block` termination. -/
  gbody_execute_block : R16Shards.TopGbodyWk.GBody.execute_block_strong
  /-- Whole-function `run_attempt` termination. -/
  gbody_run_attempt : R16Shards.TopGbodyWk.GBody.run_attempt_strong

/-- Snap-together assembly: from the two R31 statement bundles (proved by the
`ChainHandlersR31` and `WkBlockTxProcessTail` sibling lanes) every remaining
`StrongBridges` obligation closes in one application. -/
theorem strongBridgesR31Cutover_of
    (hChain : StrongBridgesR31.ChainHandlersR31Stmt)
    (hWkPtx : StrongBridgesR31.WkProcessTransactionStmt) :
    StrongBridgesR31Cutover where
  finish_child_spec := finish_child_spec_closed_r31
  ext_code_of_head := extCodeOfHeadSpec_closed_r31
  op_dispatch_chain_spec := op_dispatch_chain_spec_r31 hChain
  chain_handlers_cutover := opDispatchChainHandlersCutover_r31 hChain
  gbody_run_frames := gbody_run_frames_aligned_r31 hChain
  gbody_process_transaction_backing :=
    StrongBridgesR31.gbody_process_transaction_backing_strong_r31 hWkPtx
  gbody_process_transaction_full :=
    StrongBridgesR31.gbody_process_transaction_full_strong_r31 hWkPtx
  wk_process_transaction_strong :=
    StrongBridgesR31.wk_process_transaction_strong_r31 hWkPtx
  wk_process_transaction_logs :=
    StrongBridgesR31.wk_process_transaction_logs_r31 hWkPtx
  gbody_execute_block := gbody_execute_block_strong_r31
  gbody_run_attempt := gbody_run_attempt_strong_r31

end InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31DropIn
