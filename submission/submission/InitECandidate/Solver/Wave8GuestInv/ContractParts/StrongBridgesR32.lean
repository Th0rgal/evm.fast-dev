import InitECandidate.Solver.Wave8GuestInv.ContractParts.EvmInvR32
import InitECandidate.Solver.Wave8GuestInv.ContractParts.WitnessDbStorageR31
import InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31

/-! # Wave 8 R32 Strong Bridges (`StrongBridgesR32`)

R32 restatement of the R31 bridge layer with honest guarded premises. Where R31
carried (false) `EvmInv`-universal premises — `hdb : ∀ s, EvmInv s → WitnessDbOK s`
and `hsys : ∀ s, EvmInv s → Inside …` — R32 threads the runtime facts established
by the `GbodyRunAttempt` / `WkProcessTransaction` lanes through the R32
invariants (`EvmInvR32`, `WorldOKR32`) of `ContractParts.EvmInvR32`:

1. `EvmPreservingSpecR32` / `EvmPreservingSpecAR32` — the R14 callee-contract
   shapes with `EvmInvR32` premises and `EvmInvR32` posts.
2. Witness-DB-guarded `get_storage` / `get_storage_original` and
   system-address-guarded `emit_transfer_log` closures for both
   `EvmPreservingSpec` and `EvmPreservingSpecA` (guards instead of the R31
   false universals); the unconditional world-account closures
   (`get_account`, `ext_code_of`, `is_account_alive`, `move_ether`) are reused
   verbatim from `WitnessDbStorageR31`.
3. `WorldAccountSpecsR32` / `WorldAccountSpecsAR32` / `WorldAccountSpecsCall_g10R32`
   — the exact R31 record shapes with strengthened guards only, plus
   constructors parameterized solely by the sibling `set_storage` premises.
4. `RemainingChainHandlersR32` (the 77 chain-WF opcode fields left after the 10
   call/create-family fields) and `opDispatchChainHandlersCutover_r32`, the
   field-wise assembly of the 87-field `OpDispatchChainHandlersCutoverR32`
   of `ContractParts.EvmInvR32`; `CallSpecLiftR32` names the Slot 6
   (`Group10CallR32`) wiring lift from `Group10.OpHandlerSpecA` strength to
   `OpHandlerChainSpecR32` for the five call-family handler premises.
5. `ChainHandlersR32Stmt` — the chain-handler statement bundle, from which the
   chain-WF `OpDispatchSpecAR32` and the aligned `gbody_run_frames` bound
   (`EvmInvR32 ∧ HeadMemChainWF`) follow directly.
6. `WkProcessTransactionStmtR32` — the `process_transaction` statement bundle
   with R32-threaded sibling outputs (`TxReadyBackingStrong ∧ WorldOKR32`,
   `TxReadyFullStrong ∧ WorldOKR32`, relational strong cut on
   `TxReadyStrong ∧ WorldOKR32`), with the `RetTransactionLogs` corollary
   weakened from the strong cut. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false

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
open InitECandidate.Solver.Wave8GuestInv.ContractParts.PtxCalleesProvedR31
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
open InitECandidate.Solver.Wave8Contracts.M23 (Resumes)

/-! ## 1. R32 callee-contract shapes -/

/-- R32 callee contract: the R14 `EvmPreservingSpec` shape with the `EvmInvR32`
premise and `EvmInvR32` post. -/
def EvmPreservingSpecR32
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Qret : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      EvmInvR32 s → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      let r := (evaluateHOLFiniteState s body).1
      let post := (evaluateHOLFiniteState s body).2
      (∀ v, r = some (.returned v) →
        EvmInvR32 post ∧ evmChain post = evmChain s ∧ OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧
          Qret s v post) ∧
      (IsEvmErr r →
        EvmInvR32 post ∧ evmChain post = evmChain s ∧ OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s)

/-- R32 callee contract: the R16 `EvmPreservingSpecA` shape with `EvmInvR32` /
`Group10.HeadMemChainWF` premises and posts. -/
def EvmPreservingSpecAR32
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (Qret : ∀ {F : Type}, PanSemStateFiniteExact 64 F → ValueHOL 64 → PanSemStateFiniteExact 64 F → Prop)
    (fname : MlS) : Prop :=
  ∃ (params : List (MlS × ShapeHOL)) (body : ProgHOL 64) (retShape : ShapeHOL),
    originalRuntimeCode.lookup fname = some (params, body, retShape) ∧
    ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), s.code = originalRuntimeCode →
      EvmInvR32 s → Group10.HeadMemChainWF s → P s →
      (∃ values, lookupCodeHOLFinite originalRuntimeCode.lookup fname values =
        some (body, s.locals, retShape)) →
      (evaluateHOLFiniteState s body).1 ≠ some .timeOut →
      let r := (evaluateHOLFiniteState s body).1
      let post := (evaluateHOLFiniteState s body).2
      (∀ v, r = some (.returned v) →
        (EvmInvR32 post ∧ Group10.HeadMemChainWF post) ∧
          evmChain post = evmChain s ∧ OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s ∧ Qret s v post) ∧
      (IsEvmErr r → (EvmInvR32 post ∧ Group10.HeadMemChainWF post) ∧
        evmChain post = evmChain s ∧ OpDispatchSpec.evmR post ≤ OpDispatchSpec.evmR s)

/-! ## 2. Witness-DB-guarded `get_storage` and `get_storage_original` closures

Replays of the R31 closures with the false universal premise replaced by the
per-state `WitnessDbOK` guard: the `StrongBridges.evm_cells_get_storage_strong`
FunSpecs guard exactly `EvmInv s ∧ WitnessDbOK s`. -/

theorem evmStepCCEqR_get_storage_r32 :
    EvmStepCCEqRSpec (fun s => StorageCreateFinish.WitnessDbOK s)
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := StrongBridges.evm_cells_get_storage_strong
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc ⟨hInv, hdb⟩ hvalid hnt hres
  obtain ⟨hevm, _, hevmR, hcells⟩ := hb s hc ⟨hInv, hdb⟩ hvalid hnt hres
  refine ⟨⟨hevm, fun ec hec => ?_⟩, hevmR⟩
  obtain ⟨h24, h32, h40, _, h56⟩ := hcells ec hec
  exact ⟨h24, h32, h40, h56⟩

theorem eps_get_storage_r32 :
    EvmPreservingSpec (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage") :=
  eps_of_evmStepCCEqR_r31 (fun _ h => h) evmStepCCEqR_get_storage_r32

theorem epsA_get_storage_r32 :
    EvmPreservingSpecA (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) evmStepCCEqR_get_storage_r32

theorem evmStepCCEqR_get_storage_original_r32 :
    EvmStepCCEqRSpec (fun s => StorageCreateFinish.WitnessDbOK s)
      ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := StrongBridges.evm_cells_get_storage_original_strong
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc ⟨hInv, hdb⟩ hvalid hnt hres
  obtain ⟨hevm, _, hevmR, hcells⟩ := hb s hc ⟨hInv, hdb⟩ hvalid hnt hres
  refine ⟨⟨hevm, fun ec hec => ?_⟩, hevmR⟩
  obtain ⟨h24, h32, h40, _, h56⟩ := hcells ec hec
  exact ⟨h24, h32, h40, h56⟩

theorem eps_get_storage_original_r32 :
    EvmPreservingSpec (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage_original") :=
  eps_of_evmStepCCEqR_r31 (fun _ h => h) evmStepCCEqR_get_storage_original_r32

theorem epsA_get_storage_original_r32 :
    EvmPreservingSpecA (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage_original") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) evmStepCCEqR_get_storage_original_r32

/-! ## 3. System-address-guarded `emit_transfer_log` closures -/

private theorem lookup_emit_transfer_log_r32 :
    originalRuntimeCode.lookup (ofString "emit_transfer_log") =
      some ([(ofString "sender", .one), (ofString "recipient", .one),
             (ofString "amount", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_emit_transfer_log, .one) :=
  lookup_of_guestAst_getElem 567 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_emit_transfer_log) rfl

private theorem emit_transfer_log_params_r32 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "emit_transfer_log") vs =
      some (sourceFnBody Guest.Software.guestFn_emit_transfer_log, s.locals, .one)) :
    ∃ (sender recipient : BitVec 64) (amount : ValueHOL 64),
      s.locals.lookup (ofString "sender") = some (.val (.word sender)) ∧
      s.locals.lookup (ofString "recipient") = some (.val (.word recipient)) ∧
      s.locals.lookup (ofString "amount") = some amount := by
  obtain ⟨vals, hl⟩ := hex
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "emit_transfer_log")
    vals _ s.locals .one hl
  simp only [lookupCodeHOLExact, lookup_emit_transfer_log_r32] at hx
  rcases vals with _ | ⟨vs, _ | ⟨vr, _ | ⟨va, _ | _⟩⟩⟩
  · simp at hx
  · simp at hx
  · simp at hx
  · rcases vs with ⟨⟨sender⟩⟩ | _ | _ <;> rcases vr with ⟨⟨recipient⟩⟩ | _ | _ <;>
      try (simp [shapeOfHOLExact, shapeEqHOL] at hx)
    simp [shapeOfHOLExact, shapeEqHOL,
      show ofString "sender" ≠ ofString "recipient" by decide,
      show ofString "sender" ≠ ofString "amount" by decide,
      show ofString "recipient" ≠ ofString "amount" by decide] at hx
    have hL := hx.2
    refine ⟨sender, recipient, va, ?_, ?_, ?_⟩ <;>
      (simp only [← hL]; simp [show ofString "sender" ≠ ofString "recipient" by decide,
        show ofString "sender" ≠ ofString "amount" by decide,
        show ofString "recipient" ≠ ofString "sender" by decide,
        show ofString "recipient" ≠ ofString "amount" by decide,
        show ofString "amount" ≠ ofString "sender" by decide,
        show ofString "amount" ≠ ofString "recipient" by decide])
  · simp at hx

theorem evmStepCCEqR_emit_transfer_log_r32 :
    EvmStepCCEqRSpec (fun s => Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
      ["heap_ptr"] (ofString "emit_transfer_log") := by
  refine ⟨_, _, _, lookup_emit_transfer_log_r32, ?_⟩
  intro F s hc ⟨hInv, hsys⟩ hex hnt hr
  obtain ⟨sender, recipient, amount, hs, hrp, ha⟩ := emit_transfer_log_params_r32 hex
  obtain ⟨topic, htopic⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "transfer_topic" (by decide)
  exact emit_transfer_log_body_step_eqR_r31 s sender recipient topic amount
    hInv hsys htopic hs hrp ha hr

private theorem hp_sub_hp_sp_r32 :
    ∀ g ∈ (["heap_ptr"] : List String), g ∈ (["heap_ptr", "scratch_ptr"] : List String) := by
  intro g hg
  simp at hg ⊢
  exact Or.inl hg

theorem eps_emit_transfer_log_r32 :
    EvmPreservingSpec (fun s => Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "emit_transfer_log") :=
  eps_of_evmStepCCEqR_r31 hp_sub_hp_sp_r32 evmStepCCEqR_emit_transfer_log_r32

theorem epsA_emit_transfer_log_r32 :
    EvmPreservingSpecA (fun s => Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "emit_transfer_log") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) hp_sub_hp_sp_r32 evmStepCCEqR_emit_transfer_log_r32

/-! ## 4. R32 world-account records

The exact R31 record shapes with strengthened guards only (the witnesses carry
`WitnessDbOK` / system-address readiness; the posts stay R31-shaped). -/

/-- R32 `WorldAccountSpecs`: `get_storage` / `get_storage_original` guarded by
`WitnessDbOK`, `emit_transfer_log` guarded by system-address readiness. -/
structure WorldAccountSpecsR32 : Prop where
  eps_get_account :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_account")
  eps_ext_code_of :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "ext_code_of")
  eps_get_storage :
    EvmPreservingSpec (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage")
  eps_get_storage_original :
    EvmPreservingSpec (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage_original")
  eps_set_storage :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")
  eps_is_account_alive :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "is_account_alive")
  eps_move_ether :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "move_ether")
  eps_emit_transfer_log :
    EvmPreservingSpec (fun s => Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "emit_transfer_log")

/-- R32 `WorldAccountSpecsA`: same strengthening on the A-side records. -/
structure WorldAccountSpecsAR32 : Prop where
  epsA_get_account :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_account")
  epsA_ext_code_of :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "ext_code_of")
  epsA_get_storage :
    EvmPreservingSpecA (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage")
  epsA_get_storage_original :
    EvmPreservingSpecA (fun s => StorageCreateFinish.WitnessDbOK s)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage_original")
  epsA_set_storage :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")
  epsA_is_account_alive :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "is_account_alive")
  epsA_move_ether :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "move_ether")
  epsA_emit_transfer_log :
    EvmPreservingSpecA (fun s => Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "emit_transfer_log")

/-- R32 `WorldAccountSpecsCall_g10`: `WorldAccountSpecsAR32` strengthened with the
`ev+32` keep-word through `is_account_alive`. -/
structure WorldAccountSpecsCall_g10R32 extends WorldAccountSpecsAR32 where
  epsA_is_account_alive_k32 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "is_account_alive")

/-- `WorldAccountSpecsR32` from the sibling `set_storage` premise; every other
field is a proved closure (guarded where R31 assumed a false universal). -/
theorem worldAccountSpecsR32
    (hset : EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")) :
    WorldAccountSpecsR32 where
  eps_get_account := eps_get_account_r31
  eps_ext_code_of := eps_ext_code_of_r31
  eps_get_storage := eps_get_storage_r32
  eps_get_storage_original := eps_get_storage_original_r32
  eps_set_storage := hset
  eps_is_account_alive := eps_is_account_alive_r31
  eps_move_ether := eps_move_ether_r31
  eps_emit_transfer_log := eps_emit_transfer_log_r32

/-- `WorldAccountSpecsAR32` from the sibling A-side `set_storage` premise. -/
theorem worldAccountSpecsAR32
    (hsetA : EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")) :
    WorldAccountSpecsAR32 where
  epsA_get_account := epsA_get_account_r31
  epsA_ext_code_of := epsA_ext_code_of_r31
  epsA_get_storage := epsA_get_storage_r32
  epsA_get_storage_original := epsA_get_storage_original_r32
  epsA_set_storage := hsetA
  epsA_is_account_alive := epsA_is_account_alive_r31
  epsA_move_ether := epsA_move_ether_r31
  epsA_emit_transfer_log := epsA_emit_transfer_log_r32

/-- `WorldAccountSpecsCall_g10R32` from the sibling A-side `set_storage` premise. -/
theorem worldAccountSpecsCall_g10R32
    (hsetA : EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")) :
    WorldAccountSpecsCall_g10R32 :=
  { toWorldAccountSpecsAR32 := worldAccountSpecsAR32 hsetA
    epsA_is_account_alive_k32 := epsA_is_account_alive_k32_r31 }

/-! ## 5. The 77-field remaining chain-WF handler bundle -/

/-- Remaining R32 chain-WF handler obligations after the 10 call/create-family
fields (`op_mcopy`, `op_create`, `op_call`, `op_callcode`, `op_return`,
`op_delegatecall`, `op_create2`, `op_staticcall`, `op_revert`,
`op_selfdestruct`) are split off as individual sibling premises, so the
Slot 6 (`Group10CallR32`) call-family results wire in with zero structural
friction. -/
structure RemainingChainHandlersR32 : Prop where
  op_stop : OpHandlerChainSpecR32 (ofString "op_stop")
  op_add : OpHandlerChainSpecR32 (ofString "op_add")
  op_mul : OpHandlerChainSpecR32 (ofString "op_mul")
  op_sub : OpHandlerChainSpecR32 (ofString "op_sub")
  op_div : OpHandlerChainSpecR32 (ofString "op_div")
  op_sdiv : OpHandlerChainSpecR32 (ofString "op_sdiv")
  op_mod : OpHandlerChainSpecR32 (ofString "op_mod")
  op_smod : OpHandlerChainSpecR32 (ofString "op_smod")
  op_addmod : OpHandlerChainSpecR32 (ofString "op_addmod")
  op_mulmod : OpHandlerChainSpecR32 (ofString "op_mulmod")
  op_exp : OpHandlerChainSpecR32 (ofString "op_exp")
  op_signextend : OpHandlerChainSpecR32 (ofString "op_signextend")
  op_lt : OpHandlerChainSpecR32 (ofString "op_lt")
  op_gt : OpHandlerChainSpecR32 (ofString "op_gt")
  op_slt : OpHandlerChainSpecR32 (ofString "op_slt")
  op_sgt : OpHandlerChainSpecR32 (ofString "op_sgt")
  op_eq : OpHandlerChainSpecR32 (ofString "op_eq")
  op_iszero : OpHandlerChainSpecR32 (ofString "op_iszero")
  op_and : OpHandlerChainSpecR32 (ofString "op_and")
  op_or : OpHandlerChainSpecR32 (ofString "op_or")
  op_xor : OpHandlerChainSpecR32 (ofString "op_xor")
  op_not : OpHandlerChainSpecR32 (ofString "op_not")
  op_byte : OpHandlerChainSpecR32 (ofString "op_byte")
  op_shl : OpHandlerChainSpecR32 (ofString "op_shl")
  op_shr : OpHandlerChainSpecR32 (ofString "op_shr")
  op_sar : OpHandlerChainSpecR32 (ofString "op_sar")
  op_clz : OpHandlerChainSpecR32 (ofString "op_clz")
  op_keccak : OpHandlerChainSpecR32 (ofString "op_keccak")
  op_address : OpHandlerChainSpecR32 (ofString "op_address")
  op_balance : OpHandlerChainSpecR32 (ofString "op_balance")
  op_origin : OpHandlerChainSpecR32 (ofString "op_origin")
  op_caller : OpHandlerChainSpecR32 (ofString "op_caller")
  op_callvalue : OpHandlerChainSpecR32 (ofString "op_callvalue")
  op_calldataload : OpHandlerChainSpecR32 (ofString "op_calldataload")
  op_calldatasize : OpHandlerChainSpecR32 (ofString "op_calldatasize")
  op_calldatacopy : OpHandlerChainSpecR32 (ofString "op_calldatacopy")
  op_codesize : OpHandlerChainSpecR32 (ofString "op_codesize")
  op_codecopy : OpHandlerChainSpecR32 (ofString "op_codecopy")
  op_gasprice : OpHandlerChainSpecR32 (ofString "op_gasprice")
  op_extcodesize : OpHandlerChainSpecR32 (ofString "op_extcodesize")
  op_extcodecopy : OpHandlerChainSpecR32 (ofString "op_extcodecopy")
  op_returndatasize : OpHandlerChainSpecR32 (ofString "op_returndatasize")
  op_returndatacopy : OpHandlerChainSpecR32 (ofString "op_returndatacopy")
  op_extcodehash : OpHandlerChainSpecR32 (ofString "op_extcodehash")
  op_blockhash : OpHandlerChainSpecR32 (ofString "op_blockhash")
  op_coinbase : OpHandlerChainSpecR32 (ofString "op_coinbase")
  op_timestamp : OpHandlerChainSpecR32 (ofString "op_timestamp")
  op_number : OpHandlerChainSpecR32 (ofString "op_number")
  op_prevrandao : OpHandlerChainSpecR32 (ofString "op_prevrandao")
  op_gaslimit : OpHandlerChainSpecR32 (ofString "op_gaslimit")
  op_chainid : OpHandlerChainSpecR32 (ofString "op_chainid")
  op_selfbalance : OpHandlerChainSpecR32 (ofString "op_selfbalance")
  op_basefee : OpHandlerChainSpecR32 (ofString "op_basefee")
  op_blobhash : OpHandlerChainSpecR32 (ofString "op_blobhash")
  op_blobbasefee : OpHandlerChainSpecR32 (ofString "op_blobbasefee")
  op_slotnum : OpHandlerChainSpecR32 (ofString "op_slotnum")
  op_pop : OpHandlerChainSpecR32 (ofString "op_pop")
  op_mload : OpHandlerChainSpecR32 (ofString "op_mload")
  op_mstore : OpHandlerChainSpecR32 (ofString "op_mstore")
  op_mstore8 : OpHandlerChainSpecR32 (ofString "op_mstore8")
  op_sload : OpHandlerChainSpecR32 (ofString "op_sload")
  op_sstore : OpHandlerChainSpecR32 (ofString "op_sstore")
  op_jump : OpHandlerChainSpecR32 (ofString "op_jump")
  op_jumpi : OpHandlerChainSpecR32 (ofString "op_jumpi")
  op_pc : OpHandlerChainSpecR32 (ofString "op_pc")
  op_msize : OpHandlerChainSpecR32 (ofString "op_msize")
  op_gas : OpHandlerChainSpecR32 (ofString "op_gas")
  op_jumpdest : OpHandlerChainSpecR32 (ofString "op_jumpdest")
  op_tload : OpHandlerChainSpecR32 (ofString "op_tload")
  op_tstore : OpHandlerChainSpecR32 (ofString "op_tstore")
  op_push : OpPushBoundedChainSpecR32
  op_dup : OpHandlerChainSpecR32 (ofString "op_dup")
  op_swap : OpHandlerChainSpecR32 (ofString "op_swap")
  op_log : OpLogBoundedChainSpecR32
  op_dupn : OpHandlerChainSpecR32 (ofString "op_dupn")
  op_swapn : OpHandlerChainSpecR32 (ofString "op_swapn")
  op_exchange : OpHandlerChainSpecR32 (ofString "op_exchange")

/-! ## 6. The 87-field cutover assembly -/

/-- Field-wise assembly of the 87-field `OpDispatchChainHandlersCutoverR32`
from the 10 individual call/create-family handler premises and the 77-field
remaining bundle. -/
theorem opDispatchChainHandlersCutover_r32
    (hmcopy : OpHandlerChainSpecR32 (ofString "op_mcopy"))
    (hcreate : OpHandlerChainSpecR32 (ofString "op_create"))
    (hcall : OpHandlerChainSpecR32 (ofString "op_call"))
    (hcallcode : OpHandlerChainSpecR32 (ofString "op_callcode"))
    (hreturn : OpHandlerChainSpecR32 (ofString "op_return"))
    (hdelegatecall : OpHandlerChainSpecR32 (ofString "op_delegatecall"))
    (hcreate2 : OpHandlerChainSpecR32 (ofString "op_create2"))
    (hstaticcall : OpHandlerChainSpecR32 (ofString "op_staticcall"))
    (hrevert : OpHandlerChainSpecR32 (ofString "op_revert"))
    (hselfdestruct : OpHandlerChainSpecR32 (ofString "op_selfdestruct"))
    (hrem : RemainingChainHandlersR32) :
    OpDispatchChainHandlersCutoverR32 where
  op_stop := hrem.op_stop
  op_add := hrem.op_add
  op_mul := hrem.op_mul
  op_sub := hrem.op_sub
  op_div := hrem.op_div
  op_sdiv := hrem.op_sdiv
  op_mod := hrem.op_mod
  op_smod := hrem.op_smod
  op_addmod := hrem.op_addmod
  op_mulmod := hrem.op_mulmod
  op_exp := hrem.op_exp
  op_signextend := hrem.op_signextend
  op_lt := hrem.op_lt
  op_gt := hrem.op_gt
  op_slt := hrem.op_slt
  op_sgt := hrem.op_sgt
  op_eq := hrem.op_eq
  op_iszero := hrem.op_iszero
  op_and := hrem.op_and
  op_or := hrem.op_or
  op_xor := hrem.op_xor
  op_not := hrem.op_not
  op_byte := hrem.op_byte
  op_shl := hrem.op_shl
  op_shr := hrem.op_shr
  op_sar := hrem.op_sar
  op_clz := hrem.op_clz
  op_keccak := hrem.op_keccak
  op_address := hrem.op_address
  op_balance := hrem.op_balance
  op_origin := hrem.op_origin
  op_caller := hrem.op_caller
  op_callvalue := hrem.op_callvalue
  op_calldataload := hrem.op_calldataload
  op_calldatasize := hrem.op_calldatasize
  op_calldatacopy := hrem.op_calldatacopy
  op_codesize := hrem.op_codesize
  op_codecopy := hrem.op_codecopy
  op_gasprice := hrem.op_gasprice
  op_extcodesize := hrem.op_extcodesize
  op_extcodecopy := hrem.op_extcodecopy
  op_returndatasize := hrem.op_returndatasize
  op_returndatacopy := hrem.op_returndatacopy
  op_extcodehash := hrem.op_extcodehash
  op_blockhash := hrem.op_blockhash
  op_coinbase := hrem.op_coinbase
  op_timestamp := hrem.op_timestamp
  op_number := hrem.op_number
  op_prevrandao := hrem.op_prevrandao
  op_gaslimit := hrem.op_gaslimit
  op_chainid := hrem.op_chainid
  op_selfbalance := hrem.op_selfbalance
  op_basefee := hrem.op_basefee
  op_blobhash := hrem.op_blobhash
  op_blobbasefee := hrem.op_blobbasefee
  op_slotnum := hrem.op_slotnum
  op_pop := hrem.op_pop
  op_mload := hrem.op_mload
  op_mstore := hrem.op_mstore
  op_mstore8 := hrem.op_mstore8
  op_sload := hrem.op_sload
  op_sstore := hrem.op_sstore
  op_jump := hrem.op_jump
  op_jumpi := hrem.op_jumpi
  op_pc := hrem.op_pc
  op_msize := hrem.op_msize
  op_gas := hrem.op_gas
  op_jumpdest := hrem.op_jumpdest
  op_tload := hrem.op_tload
  op_tstore := hrem.op_tstore
  op_mcopy := hmcopy
  op_push := hrem.op_push
  op_dup := hrem.op_dup
  op_swap := hrem.op_swap
  op_log := hrem.op_log
  op_dupn := hrem.op_dupn
  op_swapn := hrem.op_swapn
  op_exchange := hrem.op_exchange
  op_create := hcreate
  op_call := hcall
  op_callcode := hcallcode
  op_return := hreturn
  op_delegatecall := hdelegatecall
  op_create2 := hcreate2
  op_staticcall := hstaticcall
  op_revert := hrevert
  op_selfdestruct := hselfdestruct

/-- The Slot 6 (`R16Shards.OpHandlersB.Group10CallR32`) wiring obligation,
parameterized on `R16Shards.OpHandlersB.OpHandlerSpecA`: Slot 6 exports
`op_call_specA_r32`, `op_callcode_specA_r32`, `op_delegatecall_specA_r32` and
`op_staticcall_specA_r32` at `R16Shards.OpHandlersB.OpHandlerSpecA`
strength (over
`WorldAccountSpecsCall_g10` / `WorldAccountSpecsA` and the
`Group10CallR32Continuations` structure, with `callSpec_generic_call_r32` /
`headMemChainWF_push` for the child-push shape). Wiring those into the R32 chain-handler statement needs this lift —
strengthening the entry guard from `EvmInv` to `EvmInvR32` (carrying
`WitnessDbOK` and the system-address `Inside` through the call body) and
aligning the posts to the R32 chain shape — for the four call ops and
`op_create2`. `ChainHandlersR32Stmt` keeps the corresponding `hop_call`,
`hop_callcode`, `hop_delegatecall`, `hop_staticcall`, `hop_create2` premises
individually named so the lifted results wire in with zero structural
friction. -/
def CallSpecLiftR32 (fname : MlS) : Prop :=
  R16Shards.OpHandlersB.OpHandlerSpecA fname → OpHandlerChainSpecR32 fname

/-! ## 7. Chain-Handler Statement Bundle (`ChainHandlersR32Stmt`) -/

/-- R32 statement bundle for the chain-handler side: the sibling `set_storage`
A-side premise, the five Group 10 callee contracts at `EvmPreservingSpecAR32`
strength, the four frame/dispatch bounds, the 10 call/create-family chain-WF
handlers, the 77-field remaining bundle, and the aligned `run_frames` bound at
`EvmInvR32 ∧ HeadMemChainWF` strength. -/
structure ChainHandlersR32Stmt : Prop where
  /-- `set_storage` preserves the journal/heap globals and `evmR` (A-side spec). -/
  hsetA : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    (ofString "set_storage")
  hU : EvmPreservingSpecAR32 (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "u256_to_be32")
  hcc : EvmPreservingSpecAR32 (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "compute_contract_address")
  hcc2 : EvmPreservingSpecAR32 (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "compute_create2_contract_address")
  hgcr : EvmPreservingSpecAR32 (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "generic_create")
  hgca : EvmPreservingSpecAR32 (fun _ => True)
    (fun s _ post => R14Shards.OpHandlersA.LocFrame s post)
    (ofString "generic_call")
  /-- `finish_child` bound (`FinishReadyA` entry). -/
  bf : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.FinishReadyA
    (ofString "finish_child") K.«finish_child»
  /-- `frame_epilogue` bound. -/
  be : TerminatingFunBoundedOn GuestInv (ofString "frame_epilogue") K.«frame_epilogue»
  /-- `frame_exception` bound. -/
  bx : TerminatingFunBoundedOn GuestInv (ofString "frame_exception") K.«frame_exception»
  /-- `op_dispatch` bound (`EvmRunA` entry). -/
  bd : TerminatingFunBoundedOn R16Shards.OpHandlersB.HeadMemBridge.EvmRunA
    (ofString "op_dispatch") K.«op_dispatch»
  /-- The 10 call/create-family chain-WF handler obligations. -/
  hop_mcopy : OpHandlerChainSpecR32 (ofString "op_mcopy")
  hop_create : OpHandlerChainSpecR32 (ofString "op_create")
  hop_call : OpHandlerChainSpecR32 (ofString "op_call")
  hop_callcode : OpHandlerChainSpecR32 (ofString "op_callcode")
  hop_return : OpHandlerChainSpecR32 (ofString "op_return")
  hop_delegatecall : OpHandlerChainSpecR32 (ofString "op_delegatecall")
  hop_create2 : OpHandlerChainSpecR32 (ofString "op_create2")
  hop_staticcall : OpHandlerChainSpecR32 (ofString "op_staticcall")
  hop_revert : OpHandlerChainSpecR32 (ofString "op_revert")
  hop_selfdestruct : OpHandlerChainSpecR32 (ofString "op_selfdestruct")
  /-- The 77 remaining R32 chain-WF handlers. -/
  hrem : RemainingChainHandlersR32
  /-- Aligned `run_frames` bound at R32 strength (`EvmInvR32 ∧ HeadMemChainWF`). -/
  hframes : TerminatingFunBoundedOn
    (fun s => EvmInvR32 s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s)
    (ofString "run_frames") K.«run_frames»

/-- `WorldAccountSpecsCall_g10R32` from the R32 statement bundle. -/
theorem worldAccountSpecsCall_g10R32_of_chainHandlers
    (hChain : ChainHandlersR32Stmt) :
    WorldAccountSpecsCall_g10R32 :=
  worldAccountSpecsCall_g10R32 hChain.hsetA

/-- Full R32 chain-WF handler cutover bundle from the statement bundle. -/
theorem opDispatchChainHandlersCutover_r32_of_stmt
    (hChain : ChainHandlersR32Stmt) :
    OpDispatchChainHandlersCutoverR32 :=
  opDispatchChainHandlersCutover_r32 hChain.hop_mcopy hChain.hop_create
    hChain.hop_call hChain.hop_callcode hChain.hop_return hChain.hop_delegatecall
    hChain.hop_create2 hChain.hop_staticcall hChain.hop_revert hChain.hop_selfdestruct
    hChain.hrem

/-- Chain-WF R32 `op_dispatch` spec (`OpDispatchSpecAR32`) from the statement
bundle. -/
theorem op_dispatch_chain_spec_r32
    (hChain : ChainHandlersR32Stmt) :
    OpDispatchSpecAR32 :=
  op_dispatch_chain_spec_cutover_r32 (opDispatchChainHandlersCutover_r32_of_stmt hChain)

/-- End-to-end aligned `gbody_run_frames` bound from the statement bundle
(re-export of the bundle's `hframes`). -/
theorem gbody_run_frames_aligned_r32
    (hChain : ChainHandlersR32Stmt) :
    TerminatingFunBoundedOn
    (fun s => EvmInvR32 s ∧ R16Shards.OpHandlersB.HeadMemBridge.HeadMemChainWF s)
    (ofString "run_frames") K.«run_frames» :=
  hChain.hframes

/-! ## 8. `process_transaction` Statement Bundle (`WkProcessTransactionStmtR32`) -/

/-- R32 statement bundle for the `process_transaction` side: the R31 sibling
premises (`set_storage`, `process_message_call` bound, legacy-unused Phase 1/2
fields, entry lifts, PMC strong/backing contracts, Phase 2/4 relational cuts,
message Bo-marks contracts) plus the R32-threaded sibling outputs — the
`gbody_process_transaction` bounds and the relational strong cut on
`TxReadyStrong ∧ WorldOKR32`. -/
structure WkProcessTransactionStmtR32 : Prop where
  /-- `set_storage` world-account premise (plain `EvmPreservingSpec`). -/
  hset : EvmPreservingSpec (fun _ => True)
    (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    (ofString "set_storage")
  /-- `set_storage` world-account premise (A-side `EvmPreservingSpecA`). -/
  hsetA : R16Shards.OpHandlersB.EvmPreservingSpecA (fun _ => True)
    (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
      OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    (ofString "set_storage")
  /-- `process_message_call` terminating bound. -/
  gb_pmc : TerminatingFunBoundedOn MsgReady (ofString "process_message_call")
    K.«process_message_call»
  /-- Legacy-unused Phase 1/2 callee fields. -/
  hleg : LegacyUnusedPtxPhase12Fields
  /-- Entry lift used by the backing cut (`TxReadyBackingStrong → TxReadyFullStrong`). -/
  hentBacking : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    R16Shards.TxReadyBackingStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s
  /-- Entry lift used by the relational cut (`TxReadyStrong → TxReadyFullStrong`). -/
  hent : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
    TxReadyStrong s → R16Shards.TopGbodyWk.TxReadyFullStrong s
  /-- `process_message_call` PMC strong contract. -/
  hwk : R16Shards.PtxP34.PmcStrong
  /-- `process_message_call` PMC backing contract. -/
  hkeep : R16Shards.PmcBackingStrong
  /-- Phase 2 relational strong cut. -/
  h2 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase2
    R16Shards.TopGbodyWk.PtxAfterPhase1 R16Shards.TopGbodyWk.PtxAfterPhase2
  /-- `process_message` Bo-marks contract. -/
  hpm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
    R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
    R16Shards.TopGbodyWk.pmcKeep
    R16Shards.TopGbodyWk.RetFrameResultMarksExactBo (ofString "process_message")
  /-- `process_create_message` Bo-marks contract. -/
  hpcm : WorldKeepsIn MsgReady R16Shards.TopGbodyWk.pmcTables
    R16Shards.TopGbodyWk.pmcRegions R16Shards.TopGbodyWk.pmcGlobals
    R16Shards.TopGbodyWk.pmcKeep
    R16Shards.TopGbodyWk.RetFrameResultMarksBo (ofString "process_create_message")
  /-- Phase 4 relational strong cut. -/
  h4 : R16Shards.TopGbodyWk.PtxRelCutStrong R13Shards.ptxPhase4
    R16Shards.TopGbodyWk.PtxAfterPhase3 R16Shards.TopGbodyWk.PtxAfterPhase4
  /-- `gbody_process_transaction` bound on `TxReadyBackingStrong ∧ WorldOKR32`. -/
  hbacking : TerminatingFunBoundedOn
    (fun s => R16Shards.TxReadyBackingStrong s ∧ WorldOKR32 s) (ofString "process_transaction")
    K.«process_transaction»
  /-- `gbody_process_transaction` bound on `TxReadyFullStrong ∧ WorldOKR32`. -/
  hfull : TerminatingFunBoundedOn
    (fun s => R16Shards.TopGbodyWk.TxReadyFullStrong s ∧ WorldOKR32 s) (ofString "process_transaction")
    K.«process_transaction»
  /-- Relational `wk_process_transaction` strong cut on `TxReadyStrong ∧ WorldOKR32`. -/
  hrel : WorldKeeps (fun s => TxReadyStrong s ∧ WorldOKR32 s)
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
        (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
        (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
        (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
        (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
        (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
        (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr",
       "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd =>
        RetTransactionLogs s r post S Nd ∧ R16Shards.TopGbodyWk.PtxRetSlices s r post S Nd)
      (ofString "process_transaction")

/-- `WorldAccountSpecsR32` from the R32 ptx bundle's `set_storage` premise. -/
theorem worldAccountSpecsR32_of_wkPtx
    (hWkPtx : WkProcessTransactionStmtR32) : WorldAccountSpecsR32 :=
  worldAccountSpecsR32 hWkPtx.hset

/-- `WorldAccountSpecsAR32` from the R32 ptx bundle's A-side `set_storage` premise. -/
theorem worldAccountSpecsAR32_of_wkPtx
    (hWkPtx : WkProcessTransactionStmtR32) : WorldAccountSpecsAR32 :=
  worldAccountSpecsAR32 hWkPtx.hsetA

/-- `WorldAccountSpecsCall_g10R32` from the R32 ptx bundle's A-side `set_storage`
premise. -/
theorem worldAccountSpecsCall_g10R32_of_wkPtx
    (hWkPtx : WkProcessTransactionStmtR32) :
    WorldAccountSpecsCall_g10R32 :=
  worldAccountSpecsCall_g10R32 hWkPtx.hsetA

/-- Full `gbody_process_transaction` on `TxReadyBackingStrong ∧ WorldOKR32`
(re-export of the bundle's `hbacking`). -/
theorem gbody_process_transaction_backing_strong_r32
    (hWkPtx : WkProcessTransactionStmtR32) :
    TerminatingFunBoundedOn
      (fun s => R16Shards.TxReadyBackingStrong s ∧ WorldOKR32 s) (ofString "process_transaction")
      K.«process_transaction» :=
  hWkPtx.hbacking

/-- Full `gbody_process_transaction` on `TxReadyFullStrong ∧ WorldOKR32`
(re-export of the bundle's `hfull`). -/
theorem gbody_process_transaction_full_strong_r32
    (hWkPtx : WkProcessTransactionStmtR32) :
    TerminatingFunBoundedOn
      (fun s => R16Shards.TopGbodyWk.TxReadyFullStrong s ∧ WorldOKR32 s) (ofString "process_transaction")
      K.«process_transaction» :=
  hWkPtx.hfull

/-- Full relational `wk_process_transaction` strong cut on
`TxReadyStrong ∧ WorldOKR32` (re-export of the bundle's `hrel`). -/
theorem wk_process_transaction_strong_r32
    (hWkPtx : WkProcessTransactionStmtR32) :
    WorldKeeps (fun s => TxReadyStrong s ∧ WorldOKR32 s)
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
        (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
        (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
        (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
        (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
        (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
        (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr",
       "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd =>
        RetTransactionLogs s r post S Nd ∧ R16Shards.TopGbodyWk.PtxRetSlices s r post S Nd)
      (ofString "process_transaction") :=
  hWkPtx.hrel

/-- Weakened `RetTransactionLogs` corollary of the R32 relational cut, matching
the legacy `wk_process_transaction` postcondition shape. -/
theorem wk_process_transaction_logs_r32
    (hWkPtx : WkProcessTransactionStmtR32) :
    WorldKeeps (fun s => TxReadyStrong s ∧ WorldOKR32 s)
      (fun s => [(globN s "b2_v", if globN s "b2_v" = 0 then 0 else 128),
        (globN s "bal_key_buf", if globN s "bal_key_buf" = 0 then 0 else 64),
        (globN s "bn_expw", if globN s "bn_expw" = 0 then 0 else 352),
        (globN s "bn_gamma", if globN s "bn_gamma" = 0 then 0 else 384),
        (globN s "evm_key_buf", if globN s "evm_key_buf" = 0 then 0 else 32),
        (globN s "keccak_pad", if globN s "keccak_pad" = 0 then 0 else 136),
        (globN s "keccak_st", if globN s "keccak_st" = 0 then 0 else 200),
        (globN s "mpt_nib_scratch", if globN s "mpt_nib_scratch" = 0 then 0 else 64),
        (globN s "pre_hdr_buf", if globN s "pre_hdr_buf" = 0 then 0 else 96),
        (globN s "rmd_h", if globN s "rmd_h" = 0 then 0 else 40),
        (globN s "rmd_pad", if globN s "rmd_pad" = 0 then 0 else 128),
        (globN s "rmd_x", if globN s "rmd_x" = 0 then 0 else 128),
        (globN s "sha_pad", if globN s "sha_pad" = 0 then 0 else 128),
        (globN s "sha_st", if globN s "sha_st" = 0 then 0 else 64),
        (globN s "sk_buf", if globN s "sk_buf" = 0 then 0 else 52),
        (globN s "u256_ws", if globN s "u256_ws" = 0 then 0 else 640)])
      ["bal_index", "bn_expw", "bn_gamma", "cur_cont", "ev", "frame_mem_ptr",
       "heap_ptr", "journal_n", "scratch_ptr", "ts"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 72]),
       ("ts", []), ("bo", [24, 32, 40, 56, 64, 72, 80])]
      (fun s r post S Nd => RetTransactionLogs s r post S Nd)
      (ofString "process_transaction") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := hWkPtx.hrel
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc hP hex hnt hr
  obtain ⟨hA, hhp, hgk, hrec, htr⟩ := hb s hc hP hex hnt hr
  refine ⟨hA, hhp, hgk, hrec, fun S Nd hWT hdisj => ?_⟩
  obtain ⟨S', Nd', hsub, hWT', hgrow, hframe, hQ⟩ := htr S Nd hWT hdisj
  exact ⟨S', Nd', hsub, hWT', hgrow, hframe, hQ.1⟩

end InitECandidate.Solver.Wave8GuestInv.ContractParts
