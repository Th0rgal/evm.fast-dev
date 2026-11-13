import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2R32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty

/-! Wave 8 R32 (GbodyRunAttemptNT2R32Cases): the three decode-empty case
premises of `GbodyRunAttemptR32Empty.hraR32_of` (`hTx`, `hWit`, `hAcc`) from
the null-tolerant `run_attempt` bound of `GbodyRunAttemptNT2R32`. Used by
`CertificateR32.certificateR32_nt2`; `certificateR32_nt2_direct` does not
need them. -/

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2R32

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
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty

/-- The tx-list-null sub-case (the `hTx` premise of
`GbodyRunAttemptR32Empty.hraR32_of`) from the null-tolerant bound. -/
theorem txNullCase_run_attempt
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn TxNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_nt2 hnt).mono (fun _ hs => hs.1)

/-- The witness-list-null sub-case (the `hWit` premise) from the
null-tolerant bound. -/
theorem witNullCase_run_attempt
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn WitNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_nt2 hnt).mono (fun _ hs => hs.1)

/-- The access-list-null sub-case (the `hAcc` premise) from the
null-tolerant bound. -/
theorem accNullCase_run_attempt
    (hnt : TerminatingFunBoundedOn GbodyRunAttemptNT2.InputReadyStrong
      (ofString "run_attempt") K.«run_attempt») :
    TerminatingFunBoundedOn AccNullCase (ofString "run_attempt") K.«run_attempt» :=
  (run_attempt_r32_nt2 hnt).mono (fun _ hs => hs.1)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptNT2R32
