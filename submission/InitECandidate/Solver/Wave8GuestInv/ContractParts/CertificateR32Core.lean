import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges
import InitECandidate.Solver.Wave8GuestInv.ContractParts.TargetR32Clean
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty
import InitECandidate.Solver.Wave8Stage.StageTransfer

/-! Wave 8 R32 (CertificateR32Core): honest certificate assembly over a
compilation witness.

`Wave8GuestInv.Certificate.certificate_of_stage_transfer` feeds the stage
transfer with `source_not_timeOut_K_pan`, which rests on the dishonest
`assembly primitives` route (`Wave8GuestInv.Target`). This module assembles
the honest replacement, parameterized only by a compilation witness with the
`ConcreteM7313` oracle table (`w`, `same`: one frozen leaf, since its only
inhabitant in the tree sits behind `InitECandidate.Proofs`, which the
`Solution` import path must not reach) and by the frozen leaf premises listed
below:

* the stage transfer is the proved
  `Wave8Stage.StageTransfer.stageTransfer w same` — it is no longer a
  premise;
* `TargetR32Clean.assemblyR32_honest` closes
  `CoveredSourceTicksConsumedBounded (K.«main» + 1)` (definitionally `K_pan`,
  cf. `Assembly.lean`) from `TargetR32Clean.mainEntryLaneR32_honest`, the
  `MainEntryR32.mainEntryR32_honest` route. It takes NO
  `ChainHandlersR32Stmt` / `WkProcessTransactionStmtR32` bundle, so nothing
  here depends on the `LocFrame`-post fields `hU`/`hcc`/`hcc2`/`hgcr`/`hgca`
  of `ChainHandlersR32Stmt` (false: the callees write memory);
* the `run_attempt` strong bound is closed by
  `GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`, and the
  decode-empty case by the spine `GbodyRunAttemptR32Empty.hraR32_of`
  (`hemptyCanon_of`), which splits it into the four null-list sub-cases.

Frozen leaf premises (9), each stated verbatim in the theorem signature:

* `hexec` — `execute_block` terminating bound at `BlockReadyExecAttemptStrong`,
* `hph` — `payload_header` terminating bound at `InputReadyNwd`,
* `wph` — `payload_header` world contract at `InputReady`,
* `wsi` — `state_init` world contract at `StateInitReady`,
* `wvhs` — `validate_headers` world contract at `WorldOK`,
* `hTx`, `hWit`, `hAcc`, `hVh` — `run_attempt` terminating bound in the four
  null-list sub-cases (`TxNullCase`, `WitNullCase`, `AccNullCase`,
  `VhNullCase` of `GbodyRunAttemptR32Empty`). -/

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

/-- The honest R32 certificate over a compilation witness `w` carrying the
`ConcreteM7313` oracle table: the campaign target
(`CoveredSourceTicksConsumedBounded K_pan`, via `assemblyR32_honest` and the
`UniformSourceClock` wrappers) feeds the proved stage transfer
`Wave8Stage.StageTransfer.stageTransfer w same`, which yields the
kernel-checked `InitE.Certificate submission (.finite K_target)`. All closed
leaves are proved theorems; the nine open leaves are explicit named
premises. -/
theorem certificateR32_of_witness
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
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
    (hTx : TerminatingFunBoundedOn GbodyRunAttemptR32Empty.TxNullCase
      (ofString "run_attempt") K.«run_attempt»)
    (hWit : TerminatingFunBoundedOn GbodyRunAttemptR32Empty.WitNullCase
      (ofString "run_attempt") K.«run_attempt»)
    (hAcc : TerminatingFunBoundedOn GbodyRunAttemptR32Empty.AccNullCase
      (ofString "run_attempt") K.«run_attempt»)
    (hVh : TerminatingFunBoundedOn GbodyRunAttemptR32Empty.VhNullCase
      (ofString "run_attempt") K.«run_attempt») :
    InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer w same
      (UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
        (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
          (assemblyR32_honest
            (mainEntryLaneR32_honest
              R32CanonicalBridges.whtrR32
              (GbodyRunAttemptR32Empty.hraR32_of
                (GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32
                  hexec hph wph wsi wvhs)
                hTx hWit hAcc hVh))))))

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
