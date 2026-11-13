import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Core
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32Close

/-! Wave 8 R32 (CertificateR32Null): the honest certificate without the
null-list `run_attempt` leaves.

`CertificateR32Core.certificateR32_of_witness` carries eight frozen leaves,
three of which (`hTx`, `hWit`, `hAcc`) are `run_attempt` bounds in the
null-list sub-cases. `GbodyRunAttemptNullR32Close` replaces the route through
the strong bound and the empty-case spine by the null-tolerant replay of
`run_attempt`, and this module restates the certificate on top of it. Nothing
else in the assembly changes.

* `certificateR32_of_witness_null` — five leaves. `hTx`, `hWit`, `hAcc` are
  gone; `hexec`, `hph`, `wph` are stated at the null-tolerant guards
  (`BlockReadyExecAttemptNull True`, `InputReadyNwdZ True`, `InputReadyZ True`
  of `GbodyRunAttemptNullR32`), where every list cell, the transaction cell
  included, may be the null pair. `wsi` and `wvhs` are verbatim.
* `certificateR32_of_witness_txNull` — six leaves. `hWit`, `hAcc` are gone;
  `hTx`, `hph`, `wph`, `wsi`, `wvhs` are verbatim; `hexec` is stated at
  `BlockReadyExecAttemptNull False` (witness / access-list / versioned-hash
  cells may be null, the transaction cell may not).

The restated leaves are not weaker obligations: each relaxed guard is implied
by the original one, so each restated leaf implies the original leaf
(`GbodyRunAttemptNullR32Close.hexec_strong_of_null`, `hph_of_z`, `wph_of_z`).
The notes on the open leaves in `CertificateR32Core` still apply to them. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Null

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

/-- The honest R32 certificate with no null-list `run_attempt` leaf: five
frozen leaves, `hexec` / `hph` / `wph` at the null-tolerant guards. -/
theorem certificateR32_of_witness_null
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.InputReadyNwdZ True)
      (ofString "payload_header") K.«payload_header»)
    (wph : WorldKeeps (GbodyRunAttemptNullR32.InputReadyZ True)
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
      R16Shards.TopGbodyWk.RetHeadersStrong (ofString "validate_headers")) :
    InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer w same
      (UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
        (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
          (assemblyR32_honest
            (mainEntryLaneR32_honest
              R32CanonicalBridges.whtrR32
              (GbodyRunAttemptNullR32Close.hraR32_null hexec hph wph wsi wvhs))))))

/-- The honest R32 certificate without the witness-null and access-list-null
`run_attempt` leaves: six frozen leaves, only `hexec` restated. -/
theorem certificateR32_of_witness_txNull
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.BlockReadyExecAttemptNull False)
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
      (ofString "run_attempt") K.«run_attempt») :
    InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer w same
      (UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
        (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
          (assemblyR32_honest
            (mainEntryLaneR32_honest
              R32CanonicalBridges.whtrR32
              (GbodyRunAttemptNullR32Close.hraR32_of_txNull hexec hph wph wsi wvhs hTx))))))

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Null
