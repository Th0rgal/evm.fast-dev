import InitE.Challenge
import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32

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

/-- The honest R32 certificate route: `hstrong` is closed by
`GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`
(`gbody_run_attempt_strong_of` with all 20 leaf premises discharged from
proved modules), and the stage transfer is fed by
`TargetR32Clean.assemblyR32`'s `CoveredSourceTicksConsumedBounded`
(`UniformSourceClock` wrappers) instead of the dishonest
`source_not_timeOut_K_pan` primitives route. The genuinely-open obligations
stay as explicit named hypotheses: the concrete oracle compilation witness
(`w`, whose `concreteOracleWitness` inhabitant lives in
`InitECandidate.Solver.ConcreteOracleWitness` behind the compiler-correctness
proof tree), the stage transfer (`hstage`, closed by
`Wave8Stage.StageTransfer.stageTransfer` once `w.oracles =
ConcreteM7313.oracles` is discharged there), the chain-handler and
`process_transaction` statement bundles (`hChain`, `hWkPtx`), the five
sub-`run_attempt` hypotheses of the strong bound (`hexec`, `hph`, `wph`,
`wsi`, `wvhs`), and the residual `run_attempt` decode-empty case
(`hempty`). No `sorry`/`admit`/`axiom`/`native_decide` is used. -/
theorem certificate
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (hstage : StageTransfer)
    (hChain : ContractParts.ChainHandlersR32Stmt)
    (hWkPtx : ContractParts.WkProcessTransactionStmtR32)
    (hexec : TerminatingFunBoundedOn R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong
      (ofString "execute_block") K.«execute_block»)
    (hph : TerminatingFunBoundedOn InputReadyNwd
      (ofString "payload_header") K.«payload_header»)
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
    (hempty : TerminatingFunBoundedOn
      ContractParts.R32CanonicalBridges.RunAttemptR32CanonEmptyCase
      (ofString "run_attempt") K.«run_attempt») :
    InitE.Certificate submission claimedScore := by
  rw [claimedScore_eq_K_target]
  exact ContractParts.CertificateR32.certificateR32
    w hstage
    hChain hWkPtx hexec hph wph wsi wvhs hempty

end InitE.Challenge
