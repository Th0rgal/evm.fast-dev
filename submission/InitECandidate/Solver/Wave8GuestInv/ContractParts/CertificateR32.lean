import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges
import InitECandidate.Solver.Wave8GuestInv.ContractParts.TargetR32Clean
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32

/-! Wave 8 R32 (CertificateR32): honest certificate assembly route.

`Wave8GuestInv.Certificate.certificate_of_stage_transfer` feeds the stage
transfer with `source_not_timeOut_K_pan`, which rests on the dishonest
`assembly primitives` route (`Wave8GuestInv.Target`). This module assembles
the honest replacement: `TargetR32Clean.assemblyR32` closes
`CoveredSourceTicksConsumedBounded (K.«main» + 1)` (definitionally
`K_pan`, cf. `Assembly.lean`) from the R32 main lane, whose `run_attempt`
strong bound is closed by
`GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`
(`gbody_run_attempt_strong_of` with all 20 leaf premises discharged from
proved modules). The remaining genuinely-open hypotheses are explicit named
premises:

* `hChain` — the chain-handler statement bundle (`ChainHandlersR32Stmt`),
* `hWkPtx` — the `process_transaction` statement bundle
  (`WkProcessTransactionStmtR32`),
* `hexec`, `hph`, `wph`, `wsi`, `wvhs` — the five sub-`run_attempt`
  hypotheses of the strong bound,
* `hempty` — the residual `run_attempt` decode-empty case at the canonical
  R32 guard (`R32CanonicalBridges.RunAttemptR32CanonEmptyCase`).

`transfer` is taken as a premise (type `Wave8GuestInv.StageTransfer`), so
this module does not depend on the `Wave8Stage` rebuild; the caller (e.g.
`Solution.lean`) supplies the closed
`Wave8Stage.StageTransfer.stageTransfer`. No `sorry`, `admit`, `axiom` or
`native_decide` is used. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Compiler.Encoders.Asm
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- The honest R32 certificate: the campaign target
(`CoveredSourceTicksConsumedBounded K_pan`, via `assemblyR32` and the
`UniformSourceClock` wrappers) feeds the stage transfer, which yields the
kernel-checked `InitE.Certificate submission (.finite K_target)`. All
closed leaves are proved theorems; the open hypotheses above are explicit
named premises. -/
theorem certificateR32
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (transfer : StageTransfer)
    (hChain : ChainHandlersR32Stmt)
    (hWkPtx : WkProcessTransactionStmtR32)
    (hexec : TerminatingFunBoundedOn R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wph : WorldKeeps InputReady
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
        (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64)])
      ["heap_ptr", "scratch_ptr", "wd_rlp_slices"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetHeader (ofString "payload_header"))
    (wsi : WorldReturnsIn StateInitReady
      (fun s => if locN s "codedb" = 0 then [] else [locN s "codedb"]) (fun _ => [])
      ["bs", "heap_ptr", "journal", "journal_cap", "journal_n", "scratch_ptr", "sk_buf", "ts", "ws"]
      [("ws", []), ("bs", []), ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      RetStateInit (ofString "state_init"))
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetHeadersStrong (ofString "validate_headers"))
    (hempty : TerminatingFunBoundedOn R32CanonicalBridges.RunAttemptR32CanonEmptyCase
      (ofString "run_attempt") K.«run_attempt») :
    InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (transfer
      (UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
        (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
          (assemblyR32
            (mainEntryLaneR32 hChain hWkPtx
              R32CanonicalBridges.whtrR32
              (R32CanonicalBridges.hraR32
                (GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32
                  hexec hph wph wsi wvhs)
                hempty))))))

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
