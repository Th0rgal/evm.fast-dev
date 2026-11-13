import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Core

/-! Wave 8 R32 (CertificateR32): honest certificate assembly route.

`certificateR32` is the R32 certificate
`InitE.Certificate submission (.finite K_target)` over a compilation witness
`w` carrying the `ConcreteM7313` oracle table (`same`). The stage transfer is
the proved `Wave8Stage.StageTransfer.stageTransfer w same` (assembled in
`CertificateR32Core.certificateR32_of_witness`), the main lane is the honest
`MainEntryR32.mainEntryR32_honest` route (no `ChainHandlersR32Stmt` /
`WkProcessTransactionStmtR32` bundle), and the `run_attempt` decode-empty
case is split by `GbodyRunAttemptR32Empty.hemptyCanon_of` into its four
null-list sub-cases.

Frozen leaf premises (9): `hexec`, `hph`, `wph`, `wsi`, `wvhs`, `hTx`,
`hWit`, `hAcc`, `hVh`; see `CertificateR32Core` for the description of
each. -/

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
`ConcreteM7313` oracle table; the nine open leaves are explicit named
premises. -/
theorem certificateR32
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
  certificateR32_of_witness w same hexec hph wph wsi wvhs hTx hWit hAcc hVh

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
