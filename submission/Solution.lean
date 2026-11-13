import InitE.Challenge
import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32Wit

set_option autoImplicit false
set_option maxRecDepth 200000
set_option exponentiation.threshold 2000

namespace InitE.Challenge

open InitECandidate.Solver.Wave8GuestInv
open Flapjack.Basis.Pure.MlString

def submission : InitE.Submission :=
  InitECandidate.Solver.Wave8GuestInv.submission

def claimedScore : InitE.NatE :=
  .finite 4485583972239622846094745952947494668730166169983861635240711046121178727100250811132783957037278517212881661013543329547

theorem claimedScore_eq_K_target :
    claimedScore = .finite K_target := rfl

/-- The honest R32 certificate route over a compilation witness `w` carrying
the `ConcreteM7313` oracle table (`same`). The stage transfer is the proved
`Wave8Stage.StageTransfer.stageTransfer w same`; the main lane is
`MainEntryWitR32.mainEntryR32_wit`, the `MainEntryR32.mainEntryR32_honest`
composition replayed with the witness-slice post of `decode_host_input`
(`DecodeSlicesR32.wk_decode_host_input_slices_sound`) carried to the
`run_attempt` call; and the `run_attempt` bound is
`GbodyRunAttemptNullR32.Wit.gbody_run_attempt_wit_r32`, the null-tolerant
replay with the `state_init` step discharged from that witness-slice fact.

The genuinely-open obligations are five frozen leaves: the compilation
witness (`w` with `same`) and four premises, the sub-`run_attempt` hypotheses
`hexec`, `hph`, `wph`, `wvhs`. `wvhs` is stated as in `CertificateR32Core`.
`hexec`, `hph` and `wph` are stated at the null-tolerant guards of
`GbodyRunAttemptNullR32`, where every list cell of the input, the transaction
cell included, may be the null pair; each of them implies the leaf of
`CertificateR32Core` it replaces, not conversely. -/
theorem certificate
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn (ContractParts.GbodyRunAttemptNullR32.BlockReadyExecAttemptNull True)
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn (ContractParts.GbodyRunAttemptNullR32.InputReadyNwdZ True)
      (ofString "payload_header")
      K.«payload_header»)
    (wph : WorldKeeps (ContractParts.GbodyRunAttemptNullR32.InputReadyZ True)
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
    InitE.Certificate submission claimedScore := by
  rw [claimedScore_eq_K_target]
  exact ContractParts.CertificateR32Wit.certificateR32_wit
    w same hexec hph wph wvhs

end InitE.Challenge
