import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
import InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
import InitECandidate.Solver.Wave8GuestInv.ContractParts.WitnessDbStorageR31

/-! # Wave 8 R32 `StrongBridgesPtxBridgeR31` (parameterized)

Canonical Shadow Integrator R32d wiring (R32c design, compile-true form). This
module bridges the R31 strong `process_transaction` closure
(`PtxCalleesProvedR31.gbody_process_transaction_full_strong_r31`, backed by the
`WitnessDbStorageR31` world-account specs) into the plain `Primitives`-world
obligations used by the top-level assembly chain, WITHOUT recompiling the
24,161-line `PtxPhase34R11.lean`.

Parameterization points (to be discharged by R32 sibling deliverables):
- `hdb`  : witness-DB slices-bounded hypothesis. Candidate closed proof:
  `WitnessDbStorageR31.worldAccountSpecs_r31` composition; once the R32
  SetStorage stack lands, bind it here as the closed `hdb`.
- `gb_pmc` : `TerminatingFunBoundedOn MsgReady (ofString "process_message_call") K.«process_message_call»`
- `hleg`  : `LegacyUnusedPtxPhase12Fields` (closed in R31 via the `ptxCalleesProvedR31` witness)
- `hwk`  : `R16Shards.PtxP34.PmcStrong`
- `hkeep`: `R16Shards.PmcBackingStrong`
- `hent` : entry enrichment (only needed for the backing-strong form below)
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000
set_option exponentiation.threshold 2000
set_option linter.dupNamespace false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesPtxBridgeR31

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
open InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31

/-- Witness-DB bound parameter: statement every R32 candidate proof must
close. Kept as an explicit hypothesis until the sibling delivery lands. -/
abbrev HdbBounded : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    WorldOK s → globN s "ws" ≠ 0 →
      R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))

/-- Bridge: the R31 full-strong `process_transaction` bound under the R32
parameter set. Every hypothesis is a named parameter so the module stays
compilable (via `lean_safe`) with any subset of siblings delivered. -/
theorem gbody_process_transaction_full_strong_r31_bridge
    (hdb : HdbBounded)
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxPhase12Fields)
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong) :
    TerminatingFunBoundedOn
      R16Shards.TopGbodyWk.TxReadyFullStrong (ofString "process_transaction")
      K.«process_transaction» :=
  gbody_process_transaction_full_strong_r31 hdb gb_pmc hleg hwk hkeep

/-- Backing-strong form (keeps `hent` explicit for consumers still on the
R29 `TxReadyBackingStrong` interface). -/
theorem gbody_process_transaction_backing_strong_r31_bridge
    (hdb : HdbBounded)
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxPhase12Fields)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong) :
    TerminatingFunBoundedOn
      R16Shards.TxReadyBackingStrong (ofString "process_transaction")
      K.«process_transaction» :=
  gbody_process_transaction_backing_strong_r31 hdb gb_pmc hleg hent hwk hkeep

end InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesPtxBridgeR31
