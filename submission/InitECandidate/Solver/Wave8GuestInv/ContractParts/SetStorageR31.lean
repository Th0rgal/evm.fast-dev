import InitECandidate.Solver.Wave8GuestInv.ContractParts.WitnessDbStorageR31
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkSetStorageR31

/-! # Wave 8 R31 `set_storage` & World-Account Specs Closure (`SetStorageR31`)

Complete R31 closure lifting `wkSc_set_storage` into:
1. `evmStepCCEqR_set_storage_r31`
2. `eps_set_storage_r31` and `epsA_set_storage_r31`
3. `worldAccountSpecs_closed_r31`, `worldAccountSpecsA_closed_r31`,
   and `worldAccountSpecsCall_g10_closed_r31`
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridges
open InitECandidate.Solver.Wave8GuestInv.EvmBase
open InitECandidate.Solver.Wave8GuestInv.EvmStepLemmas
open InitECandidate.Solver.Wave8GuestInv.EvmFrameSpecs
open InitECandidate.Solver.Wave8GuestInv.R11Shards
open InitECandidate.Solver.Wave8GuestInv.R11Shards.OpDispatchSpec
open InitECandidate.Solver.Wave8GuestInv.R14Shards.OpHandlersA
open InitECandidate.Solver.Wave8GuestInv.R16WkAcctWs
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB
open InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.HeadMemBridge

private theorem set_storage_gw_sub_r31 :
    ∀ g ∈ (["heap_ptr", "journal_n", "scratch_ptr"] : List String),
      g ∈ (["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] : List String) := by
  intro g hg
  simp at hg ⊢
  rcases hg with rfl | rfl | rfl <;> simp

theorem evmStepCCEqR_set_storage_r31 :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "set_storage") :=
  evmStepCCEqR_of_wkSc_r31 validBufList_wsAcctBufs safeStepGlobals_hp_jn_sp wkSc_set_storage

theorem eps_set_storage_r31 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage") :=
  eps_of_evmStepCCEqR_r31 set_storage_gw_sub_r31 evmStepCCEqR_set_storage_r31

theorem epsA_set_storage_r31 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) set_storage_gw_sub_r31 evmStepCCEqR_set_storage_r31

def worldAccountSpecs_closed_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    WorldAccountSpecs :=
  worldAccountSpecs_r31 hdb hsys eps_set_storage_r31

def worldAccountSpecsA_closed_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    WorldAccountSpecsA :=
  worldAccountSpecsA_r31 hdb hsys epsA_set_storage_r31

def worldAccountSpecsCall_g10_closed_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    WorldAccountSpecsCall_g10 :=
  worldAccountSpecsCall_g10_r31 hdb hsys epsA_set_storage_r31

end InitECandidate.Solver.Wave8GuestInv.ContractParts
