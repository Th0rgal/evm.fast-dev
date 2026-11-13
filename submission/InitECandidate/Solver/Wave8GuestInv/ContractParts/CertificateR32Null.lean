import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32NT
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNullR32Close

/-! Wave 8 R32 (CertificateR32Null): the R32 certificate with all three
null-list `run_attempt` leaves discharged.

`CertificateR32NT.certificateR32_nt` discharges `hWit` and `hAcc` and keeps
`hTx`, the `run_attempt` bound in the transaction-list-null decode states.
`certificateR32_null` is `certificateR32_nt` with `hTx` supplied by
`GbodyRunAttemptNullR32Close.txNullCase_run_attempt`, the replay of the
`run_attempt` proof at a guard where the transaction cell may be null too.

Its leaves are the witness (`w` with `same`) and five premises: `hexec`,
`hph`, `wph`, `wsi`, `wvhs`. `wsi` and `wvhs` are stated exactly as in
`certificateR32_of_witness`. The other three are stated at the null-tolerant
guards of `GbodyRunAttemptNullR32`, because `run_attempt` calls
`payload_header` and `execute_block` with the transaction cell still null:

* `hexec` at `BlockReadyExecAttemptNull True` (implies `hexecNT` of
  `certificateR32_nt`: `GbodyRunAttemptNullR32Close.hexecNT_of_null`),
* `hph` at `InputReadyNwdZ True` (implies the original `hph`: `hph_of_z`),
* `wph` at `InputReadyZ True` (implies the original `wph`: `wph_of_z`).

So the premise count drops from six to five, while three of the five are
stronger statements than the ones they replace. The notes on the open leaves
in `CertificateR32Core` still apply to them. -/

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

/-- The honest R32 certificate with `hTx`, `hWit` and `hAcc` discharged: the
witness leaf and five premises, `hexec` / `hph` / `wph` being stated at the
guards that allow a null transaction cell. -/
theorem certificateR32_null
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
  certificateR32_nt w same
    (GbodyRunAttemptNullR32Close.hexecNT_of_null hexec)
    (GbodyRunAttemptNullR32Close.hph_of_z hph)
    (GbodyRunAttemptNullR32Close.wph_of_z wph)
    wsi wvhs
    (GbodyRunAttemptNullR32Close.txNullCase_run_attempt hexec hph wph wsi wvhs)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
