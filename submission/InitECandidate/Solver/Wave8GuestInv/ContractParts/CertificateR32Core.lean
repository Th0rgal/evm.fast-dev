import InitECandidate.Solver.Wave8GuestInv.Certificate
import InitECandidate.Solver.Wave8GuestInv.ContractParts.R32CanonicalBridges
import InitECandidate.Solver.Wave8GuestInv.ContractParts.TargetR32Clean
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptStrongR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32Empty
import InitECandidate.Solver.Wave8Stage.StageTransfer

/-! Wave 8 R32 (CertificateR32Core): honest certificate assembly over a
compilation witness.

`Wave8GuestInv.Certificate.certificate_of_stage_transfer` feeds the stage
transfer with `source_not_timeOut_K_pan`, which rests on the dishonest
`assembly primitives` route (`Wave8GuestInv.Target`). This module assembles
the honest replacement, parameterized only by a compilation witness with the
`ConcreteM7313` oracle table (`w`, `same`: one frozen leaf, since its only
inhabitant in the tree sits behind `InitECandidate.Proofs`, which the
`Solution` import path must not reach) and by the frozen leaf premises listed
below:

* the stage transfer is the proved
  `Wave8Stage.StageTransfer.stageTransfer w same` — it is no longer a
  premise;
* `TargetR32Clean.assemblyR32_honest` closes
  `CoveredSourceTicksConsumedBounded (K.«main» + 1)` (definitionally `K_pan`,
  cf. `Assembly.lean`) from `TargetR32Clean.mainEntryLaneR32_honest`, the
  `MainEntryR32.mainEntryR32_honest` route. It takes NO
  `ChainHandlersR32Stmt` / `WkProcessTransactionStmtR32` bundle, so nothing
  here depends on the `LocFrame`-post fields `hU`/`hcc`/`hcc2`/`hgcr`/`hgca`
  of `ChainHandlersR32Stmt` (false: the callees write memory);
* the `run_attempt` strong bound is closed by
  `GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32`, and the
  decode-empty case by the spine `GbodyRunAttemptR32Empty.hraR32_of`
  (`hemptyCanon_of`), which splits it into the four null-list sub-cases;
  the vh-list-null sub-case is closed by
  `GbodyRunAttemptR32Empty.vhNullCase_run_attempt`.

Frozen leaf premises (8), each stated verbatim in the theorem signature:

* `hexec` — `execute_block` terminating bound at `BlockReadyExecAttemptStrong`,
* `hph` — `payload_header` terminating bound at `InputReadyNwd`,
* `wph` — `payload_header` world contract at `InputReady`,
* `wsi` — `state_init` world contract at `StateInitReady`,
* `wvhs` — `validate_headers` world contract at `WorldOK`,
* `hTx`, `hWit`, `hAcc` — `run_attempt` terminating bound in the three open
  null-list sub-cases (`TxNullCase`, `WitNullCase`, `AccNullCase` of
  `GbodyRunAttemptR32Empty`).

Notes on the open leaves (none of these is proved here):

* `wvhs` looks unprovable as stated. `RetHeadersStrong` asks `HeaderAt`
  (`memW (h + 136) ≤ 32`, the extra-data length) of every decoded witness
  header, but the guest's `decode_header` stores the raw extra-data length
  unchecked (`st h + 136, ex.1`) and `validate_headers` never tests it; the
  `> 32` rejection only exists in `validate_header`, for the new header.
  Weakening the post to `RetHeaders` (C03) does not help: it still asks
  `HeaderAt` of every header, and its only statement, C08's
  `wk_validate_headers`, carries no proof; the tree has no world proof of
  `validate_headers` or `decode_header` at any post. The bound is also
  really used: `RA_Parent` hands `HeaderAt` of the parent (the last witness
  header) to `ValidateHeaderReady`, because `validate_header` runs
  `header_hash(parent, tmp)` and `encode_header` copies the extra-data into
  a fixed `alloc(1024)` buffer. Dropping the leaf therefore needs new world
  proofs of `encode_header` / `header_hash` / `validate_header` for an
  unbounded parent extra-data length (or a guest-side length check in
  `decode_header`) in addition to a world proof of `validate_headers`.
* `wsi` is not reachable from `ExecBlockAndCalleeClosureR32.wsi_r32_guarded`
  at the current entry guard: its extra conjunct `NodeDbSlicesBounded` is the
  post of `wk_nodedb_build_nodedb_bounded` at `NodeDbSlicesReady`, which
  needs `WitnessSliceOK` for every witness slice, while `InputAtStrong` only
  constrains the slice-array cell itself.
* `hTx`, `hWit`, `hAcc` do not follow from `hexec`: its guard
  `BlockReadyExecAttemptStrong` contains `InputReadyStrong`, which fails
  while a run-attempt cell is null, so each of them needs an `execute_block`
  bound at a null-tolerant guard. Given one, they are no longer leaves:
  `GbodyRunAttemptNullR32` replays the strong `run_attempt` proof with the
  list cells allowed null, and `CertificateR32Null` restates this certificate
  without `hTx` / `hWit` / `hAcc` (`certificateR32_of_witness_null`, with
  `hexec`, `hph`, `wph` at the null-tolerant guards) or without `hWit` /
  `hAcc` (`certificateR32_of_witness_txNull`, with only `hexec` restated, at
  `BlockReadyExecAttemptNull False`). The theorem below is unchanged.
* `hph` reduces (`ExecBlockAndCalleeClosureR32.hph_r32_of_mpt`) to a
  `build_mpt_indexed` bound and world contract. The proved world contract
  `R16Shards.MptC10C12.wk_build_mpt_indexed_strong` is at
  `BuildMptIndexedReadyStrong`, which asks
  `memW s (slice_arr + 16 * i) + 8 ≤ heap_ptr` of every slice; at the
  transaction-list call site of `payload_header` that is a per-transaction
  pointer fact which `InputReadyNwd` does not carry.
* `wph` has only the reductions `wk_payload_header_of_bodyEffect` /
  `wk_payload_header_of_heapByteEff` in `WkHostPayloadHeaders`. The first
  asks, through `hret`, for a normal return on every `InputReady` state,
  while the guest body has a `throw BlockErr 7` path; the second asks for
  `RetHeader` of an arbitrary result. Neither premise has a supplier.
  `WkPayloadHeaderRetR32.wk_payload_header_of_bodyEffect_returned` is the
  repaired reduction (return facts asked only on the normal-return branch),
  but its body-effect premise is still open for the same reason as `hph`:
  the body calls `build_mpt_indexed` on the transaction list, and
  `InputReady` (`PayloadAt` bounds each slice length only) gives no
  per-transaction pointer fact for `BuildMptIndexedReadyStrong`.
* `hexec`: the proved `gbody_execute_block_strong` is at
  `BlockReadyExecStrong`, whose `ExecBlock.EntryAt` again asks per-item
  content bounds for the transaction list.

Common root of `wsi`, `hph`, `wph` and `hexec`: the decode post
`RetInputStrongSound` (`WkDecodeHostInputMain`) states `Inside` / `WordsOK`
only for the seven `runAttemptCells` (the list cells themselves) and says
nothing about the `(ptr, len)` items stored in them, so no per-item fact
reaches `run_attempt` through `MainEntryR32.InputReadyR32`. -/

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

/-- The honest R32 certificate over a compilation witness `w` carrying the
`ConcreteM7313` oracle table: the campaign target
(`CoveredSourceTicksConsumedBounded K_pan`, via `assemblyR32_honest` and the
`UniformSourceClock` wrappers) feeds the proved stage transfer
`Wave8Stage.StageTransfer.stageTransfer w same`, which yields the
kernel-checked `InitE.Certificate submission (.finite K_target)`. All closed
leaves are proved theorems; the eight open leaves are explicit named
premises. -/
theorem certificateR32_of_witness
    (w : LeanBridge.ConcreteOracleCompilationWitness)
    (same : w.oracles = InitECandidate.Solver.Wave8Stage.ConcreteM7313.oracles)
    (hexec : TerminatingFunBoundedOn R16Shards.TopGbodyWk.BlockReadyExecAttemptStrong
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
      (ofString "run_attempt") K.«run_attempt»)
    (hWit : TerminatingFunBoundedOn GbodyRunAttemptR32Empty.WitNullCase
      (ofString "run_attempt") K.«run_attempt»)
    (hAcc : TerminatingFunBoundedOn GbodyRunAttemptR32Empty.AccNullCase
      (ofString "run_attempt") K.«run_attempt») :
    InitE.Certificate submission (.finite K_target) :=
  LeanBridge.finite_certificate_of_witness w K_target
    (InitECandidate.Solver.Wave8Stage.StageTransfer.stageTransfer w same
      (UniformSourceClock.covered_source_uniform_not_timeOut_of_has_clock_within
        (UniformSourceClock.covered_source_has_clock_within_of_ticks_bounded
          (assemblyR32_honest
            (mainEntryLaneR32_honest
              R32CanonicalBridges.whtrR32
              (GbodyRunAttemptR32Empty.hraR32_of
                (GbodyRunAttemptStrongR32.gbody_run_attempt_strong_r32
                  hexec hph wph wsi wvhs)
                hTx hWit hAcc))))))

end InitECandidate.Solver.Wave8GuestInv.ContractParts.CertificateR32
