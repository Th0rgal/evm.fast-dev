import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Core
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2R32Cases

/-! Wave 8 R32 (CertificateR32NT2): the R32 certificate with all three
decode-empty leaves discharged.

`CertificateR32Core.certificateR32_of_witness` takes eight leaf premises
besides the compilation witness. Three of them, `hTx`, `hWit` and `hAcc`, are
`run_attempt` bounds in the tx-, witness- and access-list-null decode states.
`GbodyRunAttemptNT2R32` derives all three from the null-tolerant replay
`GbodyRunAttemptNT2` of the `run_attempt` proof, at the price of asking the
three premises whose guards contain `InputAt` at null-tolerant guards:

* `hexecNT` — the `execute_block` bound at
  `GbodyRunAttemptNT2.BlockReadyExecAttemptStrong`;
* `hphNT` — the `payload_header` bound at `GbodyRunAttemptNT2.InputReadyNwd`;
* `wphNT` — the `payload_header` world contract at
  `GbodyRunAttemptNT2.InputReady`.

`certificateR32_nt2` is `certificateR32_of_witness` with the three case
premises supplied. Its leaves are the witness (`w` with `same`) and five
premises: `hexecNT`, `hphNT`, `wphNT`, `wsi`, `wvhs`. The last two are stated
exactly as in `certificateR32_of_witness`. Each of the first three implies
the corresponding premise there (`hexec_of_nt2`, `hph_of_nt2`, `wph_of_nt2`),
not conversely: its guard also admits the states with a null list cell.

`Solution.certificate` is `certificateR32_nt2_direct`
(`CertificateR32NT2Direct.lean`), the same statement proved without the case
split.
`certificateR32_of_witness` and `certificateR32` are unchanged. -/

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
witness leaf and five premises, three of them (`hexecNT`, `hphNT`, `wphNT`)
at null-tolerant guards. -/
theorem certificateR32_nt2
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexecNT : TerminatingFunBoundedOn GbodyRunAttemptNT2.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hphNT : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyNwd (ofString "payload_header")
      K.«payload_header»)
    (wphNT : WorldKeeps GbodyRunAttemptNT2.InputReady
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
  have hnt := GbodyRunAttemptNT2R32.gbody_run_attempt_nt2_r32 hexecNT hphNT wphNT wsi wvhs
  certificateR32_of_witness w same (GbodyRunAttemptNT2R32.hexec_of_nt2 hexecNT)
    (GbodyRunAttemptNT2R32.hph_of_nt2 hphNT) (GbodyRunAttemptNT2R32.wph_of_nt2 wphNT) wsi wvhs
    (GbodyRunAttemptNT2R32.txNullCase_run_attempt hnt)
    (GbodyRunAttemptNT2R32.witNullCase_run_attempt hnt)
    (GbodyRunAttemptNT2R32.accNullCase_run_attempt hnt)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
