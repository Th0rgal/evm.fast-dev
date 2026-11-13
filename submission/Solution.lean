import InitE.Challenge
import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32NT2

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
`Wave8Stage.StageTransfer.stageTransfer w same`; the main lane is the honest
`MainEntryR32.mainEntryR32_honest` route, which takes no
`ChainHandlersR32Stmt` / `WkProcessTransactionStmtR32` bundle; `hstrong` is
closed by `GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`; and the
four null-list sub-cases of the `run_attempt` decode-empty case are all
closed: the vh-list one by `GbodyRunAttemptR32Empty.vhNullCase_run_attempt`,
the tx-, witness- and access-list ones by the null-tolerant replay
`GbodyRunAttemptNT2` of the `run_attempt` proof
(`CertificateR32.certificateR32_nt2`).

The genuinely-open obligations are six frozen leaves: the compilation
witness (`w` with `same`) and five premises, the sub-`run_attempt`
hypotheses of the strong bound. Two are stated at the original guards
(`wsi`, `wvhs`); three are stated at the null-tolerant guards of
`GbodyRunAttemptNT2`, which also cover the states with a null transaction,
witness or access-code list cell (`hexecNT`, `hphNT`, `wphNT`). Each of these
three implies the premise at the original guard
(`GbodyRunAttemptNT2R32.hexec_of_nt2`, `hph_of_nt2`, `wph_of_nt2`), not
conversely. -/
theorem certificate
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexecNT : TerminatingFunBoundedOn
      ContractParts.GbodyRunAttemptNT2.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hphNT : TerminatingFunBoundedOn ContractParts.GbodyRunAttemptNT2.InputReadyNwd
      (ofString "payload_header") K.«payload_header»)
    (wphNT : WorldKeeps ContractParts.GbodyRunAttemptNT2.InputReady
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
    InitE.Certificate submission claimedScore := by
  rw [claimedScore_eq_K_target]
  exact ContractParts.CertificateR32.certificateR32_nt2
    w same hexecNT hphNT wphNT wsi wvhs

end InitE.Challenge
