import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Core
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNTR32

/-! Wave 8 R32 (CertificateR32NT): the R32 certificate with the witness- and
access-list null leaves discharged.

`CertificateR32Core.certificateR32_of_witness` takes eight leaf premises
besides the compilation witness. Two of them, `hWit` and `hAcc`, are
`run_attempt` bounds in the witness-list-null and access-list-null decode
states. `GbodyRunAttemptNTR32` derives both from the null-tolerant replay of
the `run_attempt` proof, at the price of asking the `execute_block` bound at
the null-tolerant entry guard `GbodyRunAttemptNT.BlockReadyExecAttemptStrong`
instead of `R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong`.

`certificateR32_nt` is `certificateR32_of_witness` with those two premises
supplied. Its leaves are the witness (`w` with `same`) and six premises:
`hexecNT`, `hph`, `wph`, `wsi`, `wvhs`, `hTx`. The four in the middle and
`hTx` are stated exactly as in `certificateR32_of_witness`. `hexecNT` implies
the `hexec` premise there (`GbodyRunAttemptNTR32.hexec_of_nt`), not
conversely: its guard also admits the states whose witness, access or vh
list cell is the null pair.

This is a variant; `certificateR32_of_witness` is unchanged, and
`certificateR32` / `Solution.certificate` go through
`CertificateR32Null.certificateR32_of_witness_null`, not through this
module. -/

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

/-- The honest R32 certificate with `hWit` and `hAcc` discharged: the witness
leaf and six premises, `hexecNT` being the `execute_block` bound at the
null-tolerant entry guard. -/
theorem certificateR32_nt
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexecNT : TerminatingFunBoundedOn GbodyRunAttemptNT.BlockReadyExecAttemptStrong
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
  have hnt := GbodyRunAttemptNTR32.gbody_run_attempt_nt_r32 hexecNT hph wph wsi wvhs
  certificateR32_of_witness w same (GbodyRunAttemptNTR32.hexec_of_nt hexecNT)
    hph wph wsi wvhs hTx
    (GbodyRunAttemptNTR32.witNullCase_run_attempt hnt hTx)
    (GbodyRunAttemptNTR32.accNullCase_run_attempt hnt hTx)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
