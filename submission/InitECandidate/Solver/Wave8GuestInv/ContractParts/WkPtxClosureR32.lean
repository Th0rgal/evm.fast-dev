import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.SetStorageR31
import InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkProcessTransactionR31
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4O2
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Wire

/-! Wave 8 R32 Slot 8 (RunAttemptHtrR32), obligation C.

Closure audit and parameterized constructor for `WkProcessTransactionStmtR32`
(the `process_transaction` side of `StrongBridgesR32`).

Field-by-field audit against `ChainHandlersR32Stmt` (the chain-handler side):
the chain bundle carries only the EVM-op-side premises (`hsetA`, `hU`, `hcc`,
`hcc2`, `hgcr`, `hgca`, the frame/dispatch bounds, the 97 chain-WF handlers,
`hframes`); none of the `process_transaction`-side open premises is derivable
from it. The following fields are closed outright here:

- `hset`   := `SetStorageR31.eps_set_storage_r31` (unconditional),
- `hsetA`  := `SetStorageR31.epsA_set_storage_r31` (unconditional),
- `h4`     := `ptxPhase4_relCut_strong_of p4Run_g6 hG8` (only the `Q`-lane
  theorem `p4Run_g8` is owed by `WkPtxPhase4Q.lean`),
- `hbacking` / `hfull` := the R31 `gbody_process_transaction_*_strong_r31`
  bounds guard-weakened from `TxReadyBackingStrong` / `TxReadyFullStrong` to
  the R32 conjoined guards `… ∧ WorldOKR32` (a bound on a weaker guard is a
  bound on the stronger guard),
- `hrel`   := the R31 `wkProcessTransactionStrongStmt_of` relational cut
  guard-weakened from `TxReadyStrong` to `TxReadyStrong ∧ WorldOKR32`.

The remaining fields stay as explicit parameters of
`wkProcessTransactionStmtR32_of`: `gb_pmc`, `hleg`, `hentBacking`, `hent`,
`hdw`, `hdb`, `hwk`, `hkeep`, `h2`, `hpm`, `hpcm`, `hG8`. `hdw`/`hdb` are
stated at the concrete witness-DB instantiation
`ExtraGuard := fun _ n => NodeDbSlicesBounded · n`, so a single `hdb : HdbBounded`
serves the relational cut and both terminating bounds; once the R32
witness-DB lane lands (`worldAccountSpecs`-side closure), `hdb` can be bound
to the closed witness and the constructor becomes unconditional. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.WkPtxClosureR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
open InitECandidate.Solver.Wave8GuestInv.R13Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

/-! ### Guard-weakening helpers -/

/-- A `WorldKeeps` on guard `P` is a `WorldKeeps` on any stronger guard `P'`. -/
theorem worldKeeps_guard_mono {P P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl} {gw : List String}
    {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop} {fname : MlS}
    (h : WorldKeeps P R gw keep Q fname) (hPP' : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P' s → P s) :
    WorldKeeps P' R gw keep Q fname := by
  obtain ⟨p, b, rs, hlk, hrun⟩ := h
  exact ⟨p, b, rs, hlk, fun s hc hP' hv hnt => hrun s hc (hPP' s hP') hv hnt⟩

/-! ### The closure constructor -/

/-- `p4Run_g6` re-packed into the `PtxPhase4OStep` shape expected by the
phase-4 wire (binder order only: the wire puts `rest` and the `logs`/`succeeded`
lookups in a different order than `WkPtxPhase4O2`). -/
theorem p4Run_g6_step : R16Shards.TopGbodyWk.PtxPhase4OStep :=
  fun hD hc rest wl succw hll hsw hLL hDF hdisj hcont =>
    p4Run_g6 hD hc succw wl hsw hll hLL hDF hdisj rest hcont

/-- Witness-DB bound parameter (same statement as
`StrongBridgesPtxBridgeR31.HdbBounded`): under `WorldOK` with a non-null `ws`
global, the node-DB slices reachable from `memW s ws` are bounded. -/
abbrev HdbBounded : Prop :=
  ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    WorldOK s → globN s "ws" ≠ 0 →
      R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws"))

/-- Parameterized constructor for `WkProcessTransactionStmtR32`: every field with
a proof from the already-delivered R31/R32 lanes is closed; the open
premises are exactly the audited remainder. `hdw` is stated at the concrete
witness-DB instantiation so that the single `hdb : HdbBounded` serves all three
uses (relational cut entry, backing cut, full bound). -/
theorem wkProcessTransactionStmtR32_of
    (hdb : HdbBounded)
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxPhase12Fields)
    (hentBacking : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      TxReadyStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hdw : R16Shards.WkBalStateInit.DecodeWitnessToMptSpec
      (fun {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) =>
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s n))
    (hwk : R16Shards.PtxP34.PmcStrong)
    (hkeep : R16Shards.PmcBackingStrong)
    (h2 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase2
      R16Shards.TopGbodyWk.PtxAfterPhase1 R16Shards.TopGbodyWk.PtxAfterPhase2)
    (hpm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksExactBo (ofString "process_message"))
    (hpcm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
      R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
      R16Shards.TopGbodyWk.pmcKeep
      R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message"))
    (hG8 : R16Shards.TopGbodyWk.PtxPhase4QStep) :
    WkProcessTransactionStmtR32 where
  hset := eps_set_storage_r31
  hsetA := epsA_set_storage_r31
  gb_pmc := gb_pmc
  hleg := hleg
  hentBacking := hentBacking
  hent := hent
  hwk := hwk
  hkeep := hkeep
  h2 := h2
  hpm := hpm
  hpcm := hpcm
  h4 := ptxPhase4_relCut_strong_of p4Run_g6_step hG8
  hbacking :=
    (gbody_process_transaction_backing_strong_r31 hdb gb_pmc hleg hentBacking hwk hkeep).mono
      (fun _ h => h.1)
  hfull :=
    (gbody_process_transaction_full_strong_r31 hdb gb_pmc hleg hwk hkeep).mono
      (fun _ h => h.1)
  hrel :=
    worldKeeps_guard_mono
      (wkProcessTransactionStrongStmt_of hent hdw hdb hpm hpcm h2 p4Run_g6_step hG8)
      (fun _ h => h.1)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.WkPtxClosureR32
