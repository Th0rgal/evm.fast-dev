import InitECandidate.Solver.Wave8GuestInv.ContractParts.MainEntryR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR32
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkDecodeHostInputMain
import InitECandidate.Solver.Wave8GuestInv.EntryBridge

/-! # Wave 8 R32 Target, clean route (`TargetR32Clean`)

End-to-end R32 assembly without the `Assembly` import (which carries the
`K_pan` definition and is outside the MainEntryR32 cone). The R31 route to
the campaign target — instantiate `Assembly.assembly` over a `Primitives`
record with the eight open leaves — is UNINHABITABLE: its
`wk_decode_host_input` leaf demands the `RetInputNwd` post, whose
`RetInput` component requires unconditional `Inside` over `inputCells`; at
`ntx = 0`, `ssz_split_var_list` returns `(0, 0)` without calling `alloc`,
so the fourth cell is `(0, 0)` and `Inside (0, 0) …` fails
(`WkDecodeHostInputMain.lean` documents this counterexample at the
`RetInputIfNonempty` bridge). No honest `Primitives` record exists, and
there is no `Primitives.primitives` instance to lean on.

R32 therefore routes the end-to-end through the honest pieces only:

1. `wk_decode_host_input_r32` — the `decode_host_input` closure at
   `WorldOKR32` strength with the honest `RetInputStrongSound` post (each
   `runAttemptCells` slice is `(0, 0)` — empty list — or `Inside` the heap),
   DISCHARGED from the proved
   `WkDecodeHostInputMain.wk_decode_host_input_strong_sound` by guard
   weakening. Zero false `RetInputNwd` premises.
2. `MainEntryLaneR32` — the lane between the R32 statement bundles
   (`ChainHandlersR32Stmt`, `WkProcessTransactionStmtR32` of
   `ContractParts.StrongBridgesR32`) and the top: `main`
   terminating-bounded on the covered entry. It recomposes
   `main → verify_stateless_new_payload → attempt_l7..l1 → run_attempt`
   over `wk_decode_host_input_r32` and the R32 bundles, accepting the
   `ntx = 0` `(0, 0)` slice case at `run_attempt` entry (0 txs executes 0
   loop iterations) in place of the unconditional-`Inside` `InputReadyNwd`.
   `mainEntryLaneR32` below CLOSES this lane from the proved
   `ContractParts.MainEntryR32.mainEntryR32` composition; the only open
   premises left are the `htr_new_payload_request` world contract
   (`whtrR32`, with the `HtrNewPayloadReadyR32` R32 entry predicate) and
   the `run_attempt` terminating bound (`hra`, at `InputReadyR32`).
3. `assemblyR32` — the final step: the campaign target
   `CoveredSourceTicksConsumedBounded K_pan` follows from the main lane
   via the proved `EntryBridge` bridge; this file states it as
   `CoveredSourceTicksConsumedBounded (K.«main» + 1)`, which is
   definitionally equal to `K_pan` (`K_pan := K.«main» + 1` in
   `Assembly.lean`), stated WITHOUT importing `Assembly`.

Every premise of `assemblyR32` is honest (the open `whtrR32`/`hra` leaves
are real work, not false `Prop`s), and the file has no `Primitives` and no
`Assembly` dependency at all. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts

open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv

/-- The R32 `decode_host_input` closure: `WorldOKR32`-guarded with the honest
`RetInputStrongSound` post — every `runAttemptCells` slice of the returned
input record is `(0, 0)` (empty list: at `ntx = 0` `ssz_split_var_list`
returns `(0, 0)` without `alloc`) or `Inside` the heap and word-aligned, the
slices are disjoint from the exit world, and the payload/requests headers are
in place. Discharged from the proved
`R16Shards.TopGbodyWk.wk_decode_host_input_strong_sound` by weakening the
guard from `WorldOK` to `WorldOKR32`. -/
theorem wk_decode_host_input_r32 :
    WorldKeeps WorldOKR32
      (fun s => [(globN s "ssz_offs", if globN s "ssz_offs" = 0 then 0 else 64)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      R16Shards.TopGbodyWk.RetInputStrongSound (ofString "decode_host_input") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := R16Shards.TopGbodyWk.wk_decode_host_input_strong_sound
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc hP hex hnt hr
  exact hb s hc (WorldOKR32.worldOK hP) hex hnt hr

/-- The main lane to the campaign target, parameterized by the R32 statement
bundles whose lanes feed it: `main` terminating-bounded on the covered entry
state. This is the honest replacement for the R31 `Primitives`-record route
(whose `RetInputNwd` decode leaf is false at `ntx = 0`): the lane recomposes
`main → verify_stateless_new_payload → attempt_l7..l1 → run_attempt` over
`wk_decode_host_input_r32` (discharged above), the chain-handler bundle
`ChainHandlersR32Stmt`, and the `process_transaction` bundle
`WkProcessTransactionStmtR32`, with the `ntx = 0` `(0, 0)` slice case
accepted at `run_attempt` entry — 0 txs executes 0 loop iterations — instead
of the unconditional-`Inside` `InputReadyNwd` entry. -/
def MainEntryLaneR32 (hChain : ChainHandlersR32Stmt)
    (hWkPtx : WkProcessTransactionStmtR32) : Prop :=
  TerminatingFunBoundedOn MainEntry (ofString "main") K.«main»

/-- Closure of the R32 main lane from the proved
`ContractParts.MainEntryR32.mainEntryR32` composition (`main` recomposed
over the R32 attempt chain, the honest `RetInputStrongSound` decode
post, and the R32 statement bundles). The open premises are exactly the
two real leaves: the `htr_new_payload_request` world contract `whtrR32`
(entry predicate `MainEntryR32.HtrNewPayloadReadyR32`, the R32 weakening
of `HtrNewPayloadReady` that accepts the `ntx = 0` `(0, 0)` slice case) and
the `run_attempt` terminating bound `hra` at `MainEntryR32.InputReadyR32`.
`hChain`/`hWkPtx` are the R32 statement bundles carried as lane markers. -/
theorem mainEntryLaneR32 (hChain : ChainHandlersR32Stmt)
    (hWkPtx : WkProcessTransactionStmtR32)
    (whtrR32 : WorldKeeps MainEntryR32.HtrNewPayloadReadyR32
      (fun s => [(locN s "out", 32),
        (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]),
       ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request"))
    (hra : TerminatingFunBoundedOn MainEntryR32.InputReadyR32
      (ofString "run_attempt") K.«run_attempt») :
    MainEntryLaneR32 hChain hWkPtx :=
  MainEntryR32.mainEntryR32 hChain hWkPtx whtrR32 hra

/-- End-to-end R32 assembly: from the main lane (with the R32 statement
bundles threading `WitnessDbOK`, system-address materialization, and
`NodeDbSlicesBounded` through the strengthened invariants `EvmInvR32` /
`WorldOKR32`), the campaign target `CoveredSourceTicksConsumedBounded K_pan`
follows by the proved `EntryBridge` bridge; stated here as
`CoveredSourceTicksConsumedBounded (K.«main» + 1)`, definitionally equal to
`K_pan` (cf. `Assembly.lean`), WITHOUT importing `Assembly`. -/
theorem assemblyR32 {hChain : ChainHandlersR32Stmt}
    {hWkPtx : WkProcessTransactionStmtR32}
    (hMain : MainEntryLaneR32 hChain hWkPtx) :
    CoveredSourceTicksConsumedBounded (K.«main» + 1) :=
  coveredSourceTicksConsumedBounded_of_terminatingMainOnEntry hMain

end InitECandidate.Solver.Wave8GuestInv.ContractParts
