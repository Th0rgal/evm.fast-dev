import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Wit

/-! Wave 8 R32 (CertificateR32): honest certificate assembly route.

`certificateR32` is the R32 certificate
`InitE.Certificate submission (.finite K_target)` over a compilation witness
`w` carrying the `ConcreteM7313` oracle table (`same`). The stage transfer is
the proved `Wave8Stage.StageTransfer.stageTransfer w same`, the main lane is
`MainEntryWitR32.mainEntryR32_wit` (carrying the witness-slice post
`DecodeSlicesR32.wk_decode_host_input_slices_sound` of `decode_host_input` to
the `run_attempt` entry), and the `run_attempt` bound is
`GbodyRunAttemptNullR32.Wit.gbody_run_attempt_wit_r32` (closing both the
decode-empty null-list cases `hTx` / `hWit` / `hAcc` / `hVh` and the
`state_init` world premise `wsi`), assembled in
`CertificateR32Wit.certificateR32_wit`.

Frozen leaf premises (4): `hexec`, `hph`, `wph`, `wvhs`. -/

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
`ConcreteM7313` oracle table; the four open leaves are explicit named
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
    (wvhs : WorldKeeps WorldOK
      (fun s => [(globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200)])
      ["heap_ptr", "scratch_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetHeadersStrong (ofString "validate_headers")) :
    InitE.Certificate submission (.finite K_target) :=
  CertificateR32Wit.certificateR32_wit w same hexec hph wph wvhs

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
