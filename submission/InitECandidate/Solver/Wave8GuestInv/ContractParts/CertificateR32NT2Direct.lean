import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges
import InitECandidate.Solver.Wave8GuestInv.ContractParts.TargetR32Clean
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2R32
import InitECandidate.Solver.Wave8Stage.StageTransfer

/-! Wave 8 R32 (CertificateR32NT2Direct): `certificateR32_nt2` without the
decode-empty case split.

`certificateR32_nt2_direct` has the statement of `certificateR32_nt2`
(`CertificateR32NT2.lean`): the witness leaf (`w` with `same`) and the five
premises `hexecNT`, `hphNT`, `wphNT`, `wsi`, `wvhs`. Its proof is the term of
`CertificateR32Core.certificateR32_of_witness` with the `run_attempt` premise
of `mainEntryLaneR32_honest` supplied by `GbodyRunAttemptNT2R32.hraR32_nt2`
instead of `GbodyRunAttemptR32Empty.hraR32_of`: every R32 `run_attempt` entry
state satisfies the null-tolerant guard, so no case premise is needed. This
file imports neither `CertificateR32Core` nor `GbodyRunAttemptR32Empty`.

`Solution.certificate` is this theorem at `claimedScore`. -/

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

/-- The honest R32 certificate over the witness leaf and five premises, three
of them (`hexecNT`, `hphNT`, `wphNT`) at null-tolerant guards. Same statement
as `certificateR32_nt2`; the `run_attempt` premise of the main lane is taken
directly from `GbodyRunAttemptNT2R32.hraR32_nt2`. -/
theorem certificateR32_nt2_direct
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
  LeanBridge.finite_certificate_of_witness w K_target
    (InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer w same
      (UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
        (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
          (assemblyR32_honest
            (mainEntryLaneR32_honest
              R32CanonicalBridges.whtrR32
              (GbodyRunAttemptNT2R32.hraR32_nt2
                (GbodyRunAttemptNT2R32.gbody_run_attempt_nt2_r32
                  hexecNT hphNT wphNT wsi wvhs)))))))

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
