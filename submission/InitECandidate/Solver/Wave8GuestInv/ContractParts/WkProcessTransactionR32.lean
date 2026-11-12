import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR31
import InitECandidate.Solver.Wave8GuestInv.ContractParts.SetStorageR31
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4O2
import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkPtxPhase4Wire

/-! # Wave 8 R32 `WkProcessTransactionR32`

Construction of the R32 `process_transaction` statement bundle
(`WkProcessTransactionStmtR32`, `StrongBridgesR32`) from the R31 sibling
statement bundle (`StrongBridgesR31.WkProcessTransactionStmt`) and the proved
phase-4 lane steps.

Every field of the R32 bundle is either

* discharged from a proved module in the tree: the two `set_storage`
  world-account premises from `SetStorageR31` (`eps_set_storage_r31` /
  `epsA_set_storage_r31`), and the phase-4 relational strong cut from
  `WkPtxPhase4Wire.ptxPhase4_relCut_strong_of` over the *proved*
  `p4Run_g6` (`WkPtxPhase4O2`, adapted to the `PtxPhase4OStep` statement)
  and the *proved* stable-logs step `p4Run_g8` (`WkPtxPhase4Q6`, as
  `WkPtxPhase4Wire.ptxPhase4QStep_proved`);
* or obtained from the R31 sibling bundle (`gbody_process_transaction_backing_strong_r31`,
  `gbody_process_transaction_full_strong_r31`,
  `wk_process_transaction_strong_r31`) by pure guard strengthening
  (`TxReadyBackingStrong`/`TxReadyFullStrong`/`TxReadyStrong` → the same
  guard conjoined with `WorldOKR32`), which is sound because
  `TerminatingFunBoundedOn` and `WorldKeeps` are both contravariant in
  their entry guard.

The remaining premises (witness-DB closures, entry lifts, PMC contracts,
phase-2 cut, legacy Phase 1/2 cutover fields, message Bo-marks contracts)
stay explicit hypothesis parameters of `wkProcessTransactionStmtR32`,
exactly mirroring the R31 parameter convention
(`R31.PrimitivesProvedR31.primitivesR31`), minus the obligations closed
above (the two `set_storage` premises and both phase-4 lane steps). -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.dupNamespace false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.WkProcessTransactionR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.ContractParts
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R11Shards

/-! ## 1. Guard strengthening for `FunSpec` / `WorldKeeps`

A `FunSpec` (and hence a `WorldKeeps`, which unfolds to one) proved under an
entry guard `P` holds under every stronger entry guard `P'` with
`P' s → P s`. -/

/-- Guard strengthening for `FunSpec`: a spec proved under `P` holds under
every stronger guard `P'` implying `P`. -/
theorem funSpec_mono_guard {P P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → Prop}
    {fname : MlS} (h : FunSpec P Q fname)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P' s → P s) :
    FunSpec P' Q fname := by
  obtain ⟨params, body, ret, hlook, hb⟩ := h
  refine ⟨params, body, ret, hlook, fun s hcode hP' hex hnt =>
    hb s hcode (hle s hP') hex hnt⟩

/-- Guard strengthening for `WorldKeeps`: a cut proved under `P` holds under
every stronger guard `P'` implying `P`. -/
theorem worldKeeps_mono_guard {P P' : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {R : ∀ {F : Type}, PanSemStateFiniteExact 64 F → List Ivl} {gw : List String}
    {keep : List (String × List Nat)}
    {Q : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Option (PanSemResultExact 64) →
      PanSemStateFiniteExact 64 F → List Nat → List Nat → Prop}
    {fname : MlS} (h : WorldKeeps P R gw keep Q fname)
    (hle : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), P' s → P s) :
    WorldKeeps P' R gw keep Q fname :=
  funSpec_mono_guard h hle

/-! ## 2. The proved phase-4 `encode_receipt` step as a `PtxPhase4OStep`

`WkPtxPhase4O2.p4Run_g6` is the proved instructions-24-30 lane theorem; its
hypotheses are the `PtxPhase4OStep` hypotheses in a different order. -/

/-- The proved `p4Run_g6` (`WkPtxPhase4O2`) repackaged as the
`PtxPhase4OStep` statement expected by `ptxPhase4_relCut_strong_of`. -/
theorem ptxPhase4OStep_of_p4Run_g6 : R16Shards.TopGbodyWk.PtxPhase4OStep :=
  fun h hc rest wl succw hlogs hsucc hLL hDF hdisj htail =>
    R16Shards.TopGbodyWk.p4Run_g6 h hc succw wl hsucc hlogs hLL hDF hdisj rest htail

/-! ## 3. The R32 statement bundle -/

/-- The R32 `process_transaction` statement bundle: the R31 sibling bundle
(`StrongBridgesR31.WkProcessTransactionStmt`) with the `set_storage`
world-account premises and the phase-4 relational cut discharged from proved
modules, lifted to the R32-threaded guards
(`… ∧ WorldOKR32`). The R31 sibling bundle's remaining premises stay
explicit. -/
theorem wkProcessTransactionStmtR32
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (hdbI : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : LegacyUnusedPtxPhase12Fields)
    (hentBacking : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
    (hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      TxReadyStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s)
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
      R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message")) :
    WkProcessTransactionStmtR32 := by
  have h4 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase4
      R16Shards.TopGbodyWk.PtxAfterPhase3 R16Shards.TopGbodyWk.PtxAfterPhase4 :=
    R16Shards.TopGbodyWk.ptxPhase4_relCut_strong_of ptxPhase4OStep_of_p4Run_g6
      R16Shards.TopGbodyWk.ptxPhase4QStep_proved
  have hrec : StrongBridgesR31.WkProcessTransactionStmt :=
    { hdb := hdb, hdbI := hdbI, hsys := hsys,
      hset := eps_set_storage_r31,
      hsetA := epsA_set_storage_r31,
      gb_pmc := gb_pmc, hleg := hleg, hentBacking := hentBacking, hent := hent,
      hwk := hwk, hkeep := hkeep, h2 := h2, hpm := hpm, hpcm := hpcm,
      h4 := h4 }
  exact
    { hset := eps_set_storage_r31,
      hsetA := epsA_set_storage_r31,
      gb_pmc := gb_pmc, hleg := hleg, hentBacking := hentBacking, hent := hent,
      hwk := hwk, hkeep := hkeep, h2 := h2, hpm := hpm, hpcm := hpcm,
      h4 := h4,
      hbacking := TerminatingFunBoundedOn.mono
        (StrongBridgesR31.gbody_process_transaction_backing_strong_r31 hrec)
        (fun _ h => h.1),
      hfull := TerminatingFunBoundedOn.mono
        (StrongBridgesR31.gbody_process_transaction_full_strong_r31 hrec)
        (fun _ h => h.1),
      hrel := worldKeeps_mono_guard
        (StrongBridgesR31.wk_process_transaction_strong_r31 hrec)
        (fun _ h => h.1) }

end InitECandidate.Solver.Wave8GuestInv.ContractParts.WkProcessTransactionR32
