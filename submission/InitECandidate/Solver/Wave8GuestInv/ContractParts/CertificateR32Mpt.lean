import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Core
import InitECandidate.Solver.Wave8GuestInv.ContractParts.ExecBlockAndCalleeClosureR32

/-! Wave 8 R32 (CertificateR32Mpt): the R32 certificate with the
`payload_header` leaf reduced to `build_mpt_indexed`.

`ExecBlockAndCalleeClosureR32.hph_r32_of_mpt` closes the `hph` leaf of
`CertificateR32Core.certificateR32_of_witness` (`payload_header`
terminating-bounded at `InputReadyNwd`) from two `build_mpt_indexed` facts:
its terminating bound `hmpt` at `BuildMptIndexedReady` and its world contract
`wmpt` at `WorldOK`. `certificateR32_of_mpt` below is the certificate with
`hph` replaced by that pair.

Neither fact has a supplier in the tree at these guards. The proved world
contract `R16Shards.MptC10C12.wk_build_mpt_indexed_strong` holds at the
stronger entry guard `BuildMptIndexedReadyStrong`, not at `WorldOK`; the
bound `R16Shards.MptC10C12.gbody_build_mpt_indexed_strong` is at that same
stronger guard and is itself conditional on eleven callee premises; and no
`payload_header` composition in the tree consumes
`BuildMptIndexedReadyStrong`. So this variant trades one open leaf (`hph`)
for two (`hmpt`, `wmpt`), ten in total, and the main route
(`CertificateR32.certificateR32`) keeps `hph` as its frozen leaf. -/

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

/-- `certificateR32_of_witness` with the `hph` leaf discharged by
`ExecBlockAndCalleeClosureR32.hph_r32_of_mpt` from the two
`build_mpt_indexed` leaves `hmpt` and `wmpt`. -/
theorem certificateR32_of_mpt
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hmpt : TerminatingFunBoundedOn BuildMptIndexedReady
      (ofString "build_mpt_indexed") K.«build_mpt_indexed»)
    (wmpt : WorldKeeps WorldOK
      (fun s =>
        [(locN s "out", 32),
         (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
         (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
         (globN s "mpt_hash_scratch", if globN s "mpt_hash_scratch" = 0 then 0 else 40),
         (globN s "mpt_key_scratch", if globN s "mpt_key_scratch" = 0 then 0 else 16)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "build_mpt_indexed"))
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
      (ofString "run_attempt") K.«run_attempt») :
    InitE.Certificate submission (.finite K_target) :=
  certificateR32_of_witness w same hexec
    (ExecBlockAndCalleeClosureR32.hph_r32_of_mpt hmpt wmpt)
    wph wsi wvhs hTx hWit hAcc

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
