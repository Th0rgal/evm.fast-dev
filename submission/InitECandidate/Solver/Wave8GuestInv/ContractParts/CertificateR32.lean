import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Null

/-! Wave 8 R32 (CertificateR32): honest certificate assembly route.

`certificateR32` is the R32 certificate
`InitE.Certificate submission (.finite K_target)` over a compilation witness
`w` carrying the `ConcreteM7313` oracle table (`same`). The stage transfer is
the proved `Wave8Stage.StageTransfer.stageTransfer w same`, the main lane is
the honest `MainEntryR32.mainEntryR32_honest` route (no
`ChainHandlersR32Stmt` / `WkProcessTransactionStmtR32` bundle), and the
`run_attempt` bound at the canonical entry guard is the null-tolerant replay
`GbodyRunAttemptNullR32Close.hraR32_null`, assembled in
`CertificateR32Null.certificateR32_of_witness_null`. The decode-empty case is
no longer split into null-list sub-cases, so the `hTx` / `hWit` / `hAcc`
leaves of `CertificateR32Core.certificateR32_of_witness` do not appear.

Frozen leaf premises (5): `hexec`, `hph`, `wph`, `wsi`, `wvhs`. The last two
are stated exactly as in `CertificateR32Core`. The first three are stated at
the null-tolerant guards of `GbodyRunAttemptNullR32`
(`BlockReadyExecAttemptNull True`, `InputReadyNwdZ True`, `InputReadyZ True`),
where every list cell of the input, the transaction cell included, may be the
null pair. Those guards are implied by the ones in `CertificateR32Core`, so
each of the three is a stronger statement than the leaf it replaces
(`GbodyRunAttemptNullR32Close.hexec_strong_of_null`, `hph_of_z`, `wph_of_z`);
the notes on the open leaves in `CertificateR32Core` still apply. -/

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

/-- The honest R32 certificate over a compilation witness with the
`ConcreteM7313` oracle table; the five open leaves are explicit named
premises. -/
theorem certificateR32
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (GbodyRunAttemptNullR32.InputReadyNwdZ True)
      (ofString "payload_header")
      K.«payload_header»)
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
  CertificateR32Null.certificateR32_of_witness_null w same hexec hph wph wsi wvhs

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
