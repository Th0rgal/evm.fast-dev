import InitECandidate.Solver.Wave8GuestInv.R31.AssemblyR31
import InitECandidate.Solver.Wave8GuestInv.R31.PrimitivesProvedR31

/-! # Wave 8 R32f `TargetR31`

Source-bound target instantiated with the directly-constructed R31 primitive
instance: the end-to-end campaign theorem under the R32f parameter set (the
open premises of `primitivesR31`). Every parameter is discharged by a sibling
delivery or wired from a proved R31/R32 module inside `primitivesR31`
(`SetStorageR31` `set_storage` world-account specs, the R32 phase-4 relational
cut); the rest stay explicit hypothesis parameters. -/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option exponentiation.threshold 2000
set_option linter.dupNamespace false

namespace InitECandidate.Solver.Wave8GuestInv.R31

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded

/-- End-to-end target under the R32f parameter set: the assembly applied to
the directly-constructed R31-strong primitive instance. -/
theorem coveredSourceTicksConsumedBounded_K_pan_r31
    (hwkdhi : WkDecodeHostInputLeaf)
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      WorldOK s → globN s "ws" ≠ 0 →
        R16Shards.EvmEkFk.StorageCreateFinish.NodeDbSlicesBounded s (memW s (globN s "ws")))
    (hdbI : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → R16Shards.EvmEkFk.StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
      K.«process_message_call»)
    (hleg : InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31.LegacyUnusedPtxPhase12Fields)
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
      R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message"))
    (hG6 : R16Shards.TopGbodyWk.PtxPhase4OStep)
    (hG8 : R16Shards.TopGbodyWk.PtxPhase4QStep)
    (hpmc : WorldKeepsIn MsgReady
      (fun s => [memW s (locN s "msg" + 152), memW s (locN s "msg" + 160)])
      (fun s => (locN s "msg", 176) ::
        InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs.bufRegions
          R16Shards.TopGbodyWk.pmcSysTxBufs s)
      R16Shards.TopGbodyWk.pmcSysTxGlobals R16Shards.TopGbodyWk.pmcSysTxKeep
      R16Shards.TopGbodyWk.RetSysTxPmc (ofString "process_message_call"))
    (hS1 : S1ContR31) :
    CoveredSourceTicksConsumedBounded K_pan :=
  assemblyR31
    (primitivesR31 hwkdhi hdb hdbI hsys gb_pmc hleg hentBacking hent hwk hkeep h2
      hpm hpcm hG6 hG8 hpmc hS1)

end InitECandidate.Solver.Wave8GuestInv.R31
