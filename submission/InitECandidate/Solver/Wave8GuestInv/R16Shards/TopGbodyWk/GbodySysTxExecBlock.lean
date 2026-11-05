import InitECandidate.Solver.Wave8GuestInv.ContractParts.C18
import InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
import InitECandidate.Solver.Wave8GuestInv.R13Shards.GbodyPayloadStateInitShard

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk

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
open InitECandidate.Solver.Wave8GuestInv.R10Shards.Fast_GbodyC17ToC21
open InitECandidate.Solver.Wave8GuestInv.R13PayloadStateInit

/-! ## 1. `gbody_process_unchecked_system_transaction_strong` -/

/-- `WordSysTxLocals`, `SysTxReadyStrong`, `sysTxReadyStrong_worldOK` and `callEntryOn_sysTxReadyStrong`
now live in `ContractParts/C17.lean` (wave8 cutover rehearsal); this file keeps the `SysTxEntry` bridge. -/

theorem sysTxReadyStrong_sysTxEntry {F : Type} {s : PanSemStateFiniteExact 64 F}
    (h : SysTxReadyStrong s) : SysTxEntry s := by
  obtain ⟨hW, ht, hd, hdn⟩ := h
  have hgw := hW.1.2.2.2.2.2.2.2.2.2
  exact ⟨hW, ht, hd, hdn, hgw "vm_system_address" (by decide), hgw "be" (by decide)⟩

theorem localsOnly_sysTxReadyStrong : LocalsOnly ["target", "data", "data_n"] SysTxReadyStrong := by
  intro F s locals k hl ⟨hW, ht, hd, hdn⟩
  refine ⟨localsFree_worldOK s locals k hW, ?_, ?_, ?_⟩
  · obtain ⟨w, hw⟩ := ht; exact ⟨w, (hl "target" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hd; exact ⟨w, (hl "data" (by simp)).trans hw⟩
  · obtain ⟨w, hw⟩ := hdn; exact ⟨w, (hl "data_n" (by simp)).trans hw⟩

/-- With the ContractParts guard now `SysTxReadyStrong`, the strong statement *is*
`GBody.«process_unchecked_system_transaction»` from `ContractParts/C17.lean`. -/
abbrev GBody.«process_unchecked_system_transaction_strong» : Prop :=
  Wave8GuestInv.GBody.«process_unchecked_system_transaction»

theorem gbody_process_unchecked_system_transaction_strong :
    Wave8GuestInv.GBody.«process_unchecked_system_transaction» := by
  intro hal hext hfmr hhn hitb hmc hmn hpmc hsr hsf hte wext hnspec wmn rtmn wpmc wsf wte rtte
  refine ⟨_, _, _, R10Shards.Fast_GbodyC17ToC21.lookup_process_unchecked_system_transaction, ?_⟩
  intro F state hcode hP
  exact bounded_process_unchecked_system_transaction_wordArgs
    hal hext hfmr hhn hitb hmc hmn hpmc hsr hsf hte
    wext hnspec wmn rtmn wpmc wsf wte rtte
    state hcode (sysTxReadyStrong_sysTxEntry hP)

end InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
