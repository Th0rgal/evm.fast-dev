import InitECandidate.Solver.Wave8GuestInv.ContractParts.StrongBridgesR29
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.WkGetAccount
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.MsB4c2bWorldStepCode
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.FramePrologueCallees
import InitECandidate.Solver.Wave8GuestInv.R16Shards.OpHandlersB.Group10CallsCreatesTail4

/-! # Wave 8 R31 Witness DB, Storage, & World-Account Closure (`WitnessDbStorageR31`)

Zero-`sorry` Pillar 2 module (`ContractParts/WitnessDbStorageR31`) proving:
1. Generic world-step lifting to `R14Shards.OpHandlersA.EvmPreservingSpec`,
   `R16Shards.OpHandlersB.EvmPreservingSpecA`, and `ev + 32` cell preservation
   via `evmStep_and_cells_of_worldStepSc` + `headMemChainWF_of_evmStep` +
   `headMemChainWF_g10_iff_bridge`.
2. Unconditional `EvmPreservingSpec` and `EvmPreservingSpecA` closures for:
   - `get_account` (`wkSc_get_account`)
   - `ext_code_of` (`wkSc_ext_code_of`, including `memW post (globN s "ev" + 32)`)
   - `is_account_alive` (`wkCodeSc_is_account_alive`, including `k32` for `WorldAccountSpecsCall_g10`)
   - `move_ether` (`wkSc_move_ether`)
3. `WitnessDbOK`-guarded `get_storage` and `get_storage_original` closures for both
   `EvmPreservingSpec` and `EvmPreservingSpecA` via `StrongBridges.evm_cells_get_storage_strong`
   and `StrongBridges.evm_cells_get_storage_original_strong`.
4. System-address-ready `emit_transfer_log` closures (`EvmStepCC ["heap_ptr"]` + exact
   `evmR post = evmR s` across early-return and `alloc`/`u256_to_be32`/`log_append` tail)
   for both `EvmPreservingSpec` and `EvmPreservingSpecA`.
5. Complete constructors `worldAccountSpecs_r31`, `worldAccountSpecsA_r31`, and
   `worldAccountSpecsCall_g10_r31` parameterized only by `hdb`, `hsys`, and `set_storage`.
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
open InitECandidate.Solver.Wave8Contracts.M23 (Resumes)

/-! ## 1. Resumption, WorldOK, and Generic Cell-Step -> `EvmPreservingSpec` / `EvmPreservingSpecA` Bridges -/

private theorem resumes_of_returned_r31 {v : ValueHOL 64}
    {r : Option (PanSemResultExact 64)} (hr : r = some (.returned v)) :
    Resumes r :=
  Or.inl ⟨v, hr⟩

private theorem resumes_of_isEvmErr_r31
    {r : Option (PanSemResultExact 64)} (hr : IsEvmErr r) :
    Resumes r := by
  obtain ⟨ev, hev⟩ := hr
  exact Or.inr ⟨ofString "EvmErr", ev, hev, by decide⟩

private theorem worldOK_of_evmInv_r31 {F : Type} (s : PanSemStateFiniteExact 64 F) (h : EvmInv s) :
    WorldOK s :=
  ⟨h.1, let ⟨S, hInvAt⟩ := h.2; ⟨S, hInvAt.1⟩⟩

private theorem head_in_evmChain_r31 {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (globN s "ev", globN s "cur_cont") ∈ evmChain s :=
  List.mem_cons_self

private theorem globalsKept_mono_r31 {F : Type} {gw1 gw2 : List String}
    {s post : PanSemStateFiniteExact 64 F}
    (hsub : ∀ g ∈ gw1, g ∈ gw2)
    (hk : GlobalsKept gw1 s post) :
    GlobalsKept gw2 s post := by
  intro k hk2
  apply hk k
  intro hk1
  obtain ⟨g, hg1, rfl⟩ := List.mem_map.1 hk1
  exact hk2 (List.mem_map.2 ⟨g, hsub g hg1, rfl⟩)

/-- Bundle capturing `EvmStepCC gw`, `evmR post = evmR s`, for any resuming execution of `fname`
under `EvmInv` + `P`. -/
def EvmStepCCEqRSpec
    (P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop)
    (gw : List String) (fname : MlS) : Prop :=
  FunSpec (fun s => EvmInv s ∧ P s)
    (fun s r post => Resumes r →
      EvmStepCC gw s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
    fname

theorem eps_of_evmStepCCEqR_r31
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw gwOut : List String} {fname : MlS}
    (hsub : ∀ g ∈ gw, g ∈ gwOut)
    (hspec : EvmStepCCEqRSpec P gw fname) :
    EvmPreservingSpec P
      (fun s _ post => GlobalsKept gwOut s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      fname := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := hspec
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc hInv hP hvalid hnt
  constructor
  · intro v hrv
    obtain ⟨⟨hst, _⟩, hrEq⟩ := hb s hc ⟨hInv, hP⟩ hvalid hnt (resumes_of_returned_r31 hrv)
    exact ⟨hst.1, hst.2.2.2, le_of_eq hrEq, globalsKept_mono_r31 hsub hst.2.2.1, hrEq⟩
  · intro herr
    obtain ⟨⟨hst, _⟩, hrEq⟩ := hb s hc ⟨hInv, hP⟩ hvalid hnt (resumes_of_isEvmErr_r31 herr)
    exact ⟨hst.1, hst.2.2.2, le_of_eq hrEq⟩

theorem epsA_of_evmStepCCEqR_r31
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw gwOut : List String} {fname : MlS}
    (hev_gw : ofString "ev" ∉ gw.map ofString)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hsub : ∀ g ∈ gw, g ∈ gwOut)
    (hspec : EvmStepCCEqRSpec P gw fname) :
    EvmPreservingSpecA P
      (fun s _ post => GlobalsKept gwOut s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      fname := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := hspec
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc hInv hWFg10 hP hvalid hnt
  have hWF : HeadMemBridge.HeadMemChainWF s := (headMemChainWF_g10_iff_bridge s).mp hWFg10
  constructor
  · intro v hrv
    obtain ⟨⟨hst, hcc⟩, hrEq⟩ := hb s hc ⟨hInv, hP⟩ hvalid hnt (resumes_of_returned_r31 hrv)
    have hWF' : HeadMemBridge.HeadMemChainWF _ :=
      headMemChainWF_of_evmStep hWF hst hev_gw hfmp_gw hcc
    exact ⟨⟨hst.1, (headMemChainWF_g10_iff_bridge _).mpr hWF'⟩,
      hst.2.2.2, le_of_eq hrEq, globalsKept_mono_r31 hsub hst.2.2.1, hrEq⟩
  · intro herr
    obtain ⟨⟨hst, hcc⟩, hrEq⟩ := hb s hc ⟨hInv, hP⟩ hvalid hnt (resumes_of_isEvmErr_r31 herr)
    have hWF' : HeadMemBridge.HeadMemChainWF _ :=
      headMemChainWF_of_evmStep hWF hst hev_gw hfmp_gw hcc
    exact ⟨⟨hst.1, (headMemChainWF_g10_iff_bridge _).mpr hWF'⟩,
      hst.2.2.2, le_of_eq hrEq⟩

theorem epsA_k32_of_evmStepCCEqR_r31
    {P : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop}
    {gw gwOut : List String} {fname : MlS}
    (hev_gw : ofString "ev" ∉ gw.map ofString)
    (hfmp_gw : ofString "frame_mem_ptr" ∉ gw.map ofString)
    (hsub : ∀ g ∈ gw, g ∈ gwOut)
    (hspec : EvmStepCCEqRSpec P gw fname) :
    EvmPreservingSpecA P
      (fun s _ post => GlobalsKept gwOut s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      fname := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := hspec
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc hInv hWFg10 hP hvalid hnt
  have hWF : HeadMemBridge.HeadMemChainWF s := (headMemChainWF_g10_iff_bridge s).mp hWFg10
  constructor
  · intro v hrv
    obtain ⟨⟨hst, hcc⟩, hrEq⟩ := hb s hc ⟨hInv, hP⟩ hvalid hnt (resumes_of_returned_r31 hrv)
    have hWF' : HeadMemBridge.HeadMemChainWF _ :=
      headMemChainWF_of_evmStep hWF hst hev_gw hfmp_gw hcc
    have hk32 := (hcc (globN s "ev", globN s "cur_cont") (head_in_evmChain_r31 s)).2.1
    exact ⟨⟨hst.1, (headMemChainWF_g10_iff_bridge _).mpr hWF'⟩,
      hst.2.2.2, le_of_eq hrEq, globalsKept_mono_r31 hsub hst.2.2.1, hrEq, hk32⟩
  · intro herr
    obtain ⟨⟨hst, hcc⟩, hrEq⟩ := hb s hc ⟨hInv, hP⟩ hvalid hnt (resumes_of_isEvmErr_r31 herr)
    have hWF' : HeadMemBridge.HeadMemChainWF _ :=
      headMemChainWF_of_evmStep hWF hst hev_gw hfmp_gw hcc
    exact ⟨⟨hst.1, (headMemChainWF_g10_iff_bridge _).mpr hWF'⟩,
      hst.2.2.2, le_of_eq hrEq⟩

/-- Lift any `WorldKeepsSc WorldOK` callee to `EvmStepCCEqRSpec (fun _ => True)`. -/
theorem evmStepCCEqR_of_wkSc_r31
    {B : BufList} {gw : List String} {fname : MlS}
    (hB : ValidBufList B) (hgw : SafeStepGlobals gw)
    (hwk : WorldKeepsSc WorldOK (bufRegions B) gw EvmBase.stdKeep NoExtra fname) :
    EvmStepCCEqRSpec (fun _ => True) gw fname := by
  obtain ⟨ps, body, rt, hlk, hbody⟩ := hwk
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc ⟨hInv, _⟩ hvalid hnt hres
  obtain ⟨hAs, S, hInvAt⟩ := hInv
  have hstep := hbody s hc ⟨hAs, S, hInvAt.1⟩ hvalid hnt hres
  obtain ⟨hevm, hevmR, hcells⟩ :=
    StorageCreateFinish.evmStep_and_cells_of_worldStepSc hB hgw hAs ⟨S, hInvAt⟩ hstep
  refine ⟨⟨hevm, fun ec hec => ?_⟩, hevmR⟩
  obtain ⟨h24, h32, h40, _, h56⟩ := hcells ec hec
  exact ⟨h24, h32, h40, h56⟩

/-! ## 2. Unconditional Closures: `get_account`, `ext_code_of`, `is_account_alive`, `move_ether` -/

theorem evmStepCCEqR_get_account_r31 :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr", "scratch_ptr"] (ofString "get_account") :=
  evmStepCCEqR_of_wkSc_r31 validBufList_wsAcctBufs safeStepGlobals_hp_sp wkSc_get_account

theorem eps_get_account_r31 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_account") :=
  eps_of_evmStepCCEqR_r31 (fun _ h => h) evmStepCCEqR_get_account_r31

theorem epsA_get_account_r31 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_account") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) evmStepCCEqR_get_account_r31

theorem evmStepCCEqR_ext_code_of_r31 :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr", "scratch_ptr"] (ofString "ext_code_of") :=
  evmStepCCEqR_of_wkSc_r31 validBufList_extCodeBufs safeStepGlobals_hp_sp wkSc_ext_code_of

theorem eps_ext_code_of_r31 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "ext_code_of") :=
  eps_of_evmStepCCEqR_r31 (fun _ h => h) evmStepCCEqR_ext_code_of_r31

theorem epsA_ext_code_of_r31 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "ext_code_of") :=
  epsA_k32_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) evmStepCCEqR_ext_code_of_r31

theorem wkSc_is_account_alive_r31 :
    WorldKeepsSc WorldOK (bufRegions wsAcctBufs)
      ["heap_ptr", "scratch_ptr"] EvmBase.stdKeep NoExtra (ofString "is_account_alive") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := wkCodeSc_is_account_alive
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc hW hex hnt hres
  have hcodeSc := hb s hc hW hex hnt hres
  obtain ⟨⟨hA, hhp, hgk, hsk, htr⟩, hsc⟩ := hcodeSc.1
  refine ⟨⟨hA, hhp, hgk, hsk, fun S Nd hWT hdisj => ?_⟩, hsc⟩
  obtain ⟨S', Nd', hsub, hWT', hgrows, hframe, _⟩ := htr S Nd hWT hdisj
  exact ⟨S', Nd', hsub, hWT', hgrows, hframe, trivial⟩

theorem evmStepCCEqR_is_account_alive_r31 :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr", "scratch_ptr"] (ofString "is_account_alive") :=
  evmStepCCEqR_of_wkSc_r31 validBufList_wsAcctBufs safeStepGlobals_hp_sp wkSc_is_account_alive_r31

theorem eps_is_account_alive_r31 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "is_account_alive") :=
  eps_of_evmStepCCEqR_r31 (fun _ h => h) evmStepCCEqR_is_account_alive_r31

theorem epsA_is_account_alive_r31 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "is_account_alive") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) evmStepCCEqR_is_account_alive_r31

theorem epsA_is_account_alive_k32_r31 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s ∧
        memW post (globN s "ev" + 32) = memW s (globN s "ev" + 32))
      (ofString "is_account_alive") :=
  epsA_k32_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) evmStepCCEqR_is_account_alive_r31

theorem evmStepCCEqR_move_ether_r31 :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr", "journal_n", "scratch_ptr"] (ofString "move_ether") :=
  evmStepCCEqR_of_wkSc_r31 validBufList_acctMutBufs safeStepGlobals_hp_jn_sp EvmEkFkPrologue.wkSc_move_ether

private theorem move_ether_gw_sub_r31 :
    ∀ g ∈ (["heap_ptr", "journal_n", "scratch_ptr"] : List String),
      g ∈ (["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] : List String) := by
  intro g hg
  simp at hg ⊢
  rcases hg with rfl | rfl | rfl <;> simp

theorem eps_move_ether_r31 :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "move_ether") :=
  eps_of_evmStepCCEqR_r31 move_ether_gw_sub_r31 evmStepCCEqR_move_ether_r31

theorem epsA_move_ether_r31 :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "move_ether") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) move_ether_gw_sub_r31 evmStepCCEqR_move_ether_r31

/-! ## 3. `WitnessDbOK`-Guarded `get_storage` and `get_storage_original` Closures -/

theorem evmStepCCEqR_get_storage_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s) :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr", "scratch_ptr"] (ofString "get_storage") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := StrongBridges.evm_cells_get_storage_strong
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc ⟨hInv, _⟩ hvalid hnt hres
  obtain ⟨hevm, _, hevmR, hcells⟩ := hb s hc ⟨hInv, hdb s hInv⟩ hvalid hnt hres
  refine ⟨⟨hevm, fun ec hec => ?_⟩, hevmR⟩
  obtain ⟨h24, h32, h40, _, h56⟩ := hcells ec hec
  exact ⟨h24, h32, h40, h56⟩

theorem eps_get_storage_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s) :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage") :=
  eps_of_evmStepCCEqR_r31 (fun _ h => h) (evmStepCCEqR_get_storage_r31 hdb)

theorem epsA_get_storage_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s) :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) (evmStepCCEqR_get_storage_r31 hdb)

theorem evmStepCCEqR_get_storage_original_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s) :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr", "scratch_ptr"] (ofString "get_storage_original") := by
  obtain ⟨ps, body, rt, hlk, hb⟩ := StrongBridges.evm_cells_get_storage_original_strong
  refine ⟨ps, body, rt, hlk, ?_⟩
  intro F s hc ⟨hInv, _⟩ hvalid hnt hres
  obtain ⟨hevm, _, hevmR, hcells⟩ := hb s hc ⟨hInv, hdb s hInv⟩ hvalid hnt hres
  refine ⟨⟨hevm, fun ec hec => ?_⟩, hevmR⟩
  obtain ⟨h24, h32, h40, _, h56⟩ := hcells ec hec
  exact ⟨h24, h32, h40, h56⟩

theorem eps_get_storage_original_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s) :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage_original") :=
  eps_of_evmStepCCEqR_r31 (fun _ h => h) (evmStepCCEqR_get_storage_original_r31 hdb)

theorem epsA_get_storage_original_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s) :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "get_storage_original") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) (fun _ h => h) (evmStepCCEqR_get_storage_original_r31 hdb)

/-! ## 4. `emit_transfer_log` Exact `evmR` & `EvmStepCC` Closure -/

private theorem lookup_emit_transfer_log_r31 :
    originalRuntimeCode.lookup (ofString "emit_transfer_log") =
      some ([(ofString "sender", .one), (ofString "recipient", .one),
             (ofString "amount", .comb [.one, .one, .one, .one])],
        sourceFnBody Guest.Software.guestFn_emit_transfer_log, .one) :=
  lookup_of_guestAst_getElem 567 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_emit_transfer_log) rfl

private theorem lookup_log_append_r31 :
    originalRuntimeCode.lookup (ofString "log_append") =
      some ([(ofString "e", .one), (ofString "log", .one)],
        sourceFnBody Guest.Software.guestFn_log_append, .one) :=
  lookup_of_guestAst_getElem 523 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_log_append) rfl

private theorem emit_transfer_log_params_r31 {F : Type} {s : PanSemStateFiniteExact 64 F}
    (hex : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "emit_transfer_log") vs =
      some (sourceFnBody Guest.Software.guestFn_emit_transfer_log, s.locals, .one)) :
    ∃ (sender recipient : BitVec 64) (amount : ValueHOL 64),
      s.locals.lookup (ofString "sender") = some (.val (.word sender)) ∧
      s.locals.lookup (ofString "recipient") = some (.val (.word recipient)) ∧
      s.locals.lookup (ofString "amount") = some amount := by
  obtain ⟨vals, hl⟩ := hex
  have hx := lookupCodeHOLFinite_eq_some originalRuntimeCode.lookup (ofString "emit_transfer_log")
    vals _ s.locals .one hl
  simp only [lookupCodeHOLExact, lookup_emit_transfer_log_r31] at hx
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

private theorem memW_with_locals_clock_r31 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (L : HolFiniteMapExact MlS (ValueHOL 64)) (k a : Nat) :
    memW { s with locals := L, clock := k } a = memW s a := rfl

private theorem evmR_of_accumulated_frame_r31 {F : Type}
    {s post : PanSemStateFiniteExact 64 F}
    (hInv : EvmInv s) (hstep : EvmEkFkPrologue.EvmStepCC ["heap_ptr"] s post)
    (hbe : post.be = s.be)
    (hout : ∀ a : BitVec 64, ¬ s.memaddrs a → post.memory a = s.memory a)
    (hbyte : ∀ b : Nat, b < 2 ^ 64 →
      ¬ (globN s "heap_ptr" ≤ b ∧ b < globN post "heap_ptr") → memB post b = memB s b) :
    OpDispatchSpec.evmR post = OpDispatchSpec.evmR s := by
  obtain ⟨_, S, _, _, _, _, frames, _⟩ := (evmInv_iff_at s).1 hInv
  refine evmR_eq_of_chain_and_words hstep.1.2.2.2 (fun ec hec => ?_)
  have fw := frames ec hec
  have hal : Allocated s (ec.1, 280) := Or.inr (fw.1 (ec.1, 280) (by simp)).1
  exact ⟨EvmEkFkPrologue.transfer_memW_of_allocated_frame hInv hstep hbe hout hbyte hal
      (ec.1 + 64) (by dsimp only; omega) (by dsimp only; omega),
    EvmEkFkPrologue.transfer_memW_of_allocated_frame hInv hstep hbe hout hbyte hal
      (ec.1 + 192) (by dsimp only; omega) (by dsimp only; omega)⟩

private theorem transfer_call0_no_return_r31 {F : Type} (s : PanSemStateFiniteExact 64 F)
    (fn : MlS) (args : List (ExpHOL 64)) (u : ValueHOL 64) :
    (evaluateHOLFiniteState s (.call (some (none, none)) fn args)).1 ≠ some (.returned u) := by
  rw [evaluateHOLFiniteState_call]
  rcases evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args with _ | _
  · simp
  · dsimp only
    rcases lookupCodeHOLFinite s.code.lookup fn _ with _ | ⟨_, _, _⟩
    · simp
    · dsimp only; split
      · simp
      · rcases evaluateHOLFiniteState _ _ with ⟨res, _⟩
        rcases res with _ | r
        · simp
        · cases r with
          | returned _ => dsimp only; split <;> simp
          | _ => simp

private theorem log_append_tail_evmR_eq_r31 {F : Type}
    (mid : PanSemStateFiniteExact 64 F) (evw logw : BitVec 64)
    (hInv : EvmInv mid)
    (hev : mid.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (hl : mid.locals.lookup (ofString "log") = some (.val (.word logw)))
    (hstepTail : EvmEkFkPrologue.EvmStepCC ["heap_ptr"] mid
      (evaluateHOLFiniteState mid EvmEkFkPrologue.transferAppendReturn).2)
    (hres : ∃ v, (evaluateHOLFiniteState mid EvmEkFkPrologue.transferAppendReturn).1 = some (.returned v)) :
    OpDispatchSpec.evmR (evaluateHOLFiniteState mid EvmEkFkPrologue.transferAppendReturn).2 =
      OpDispatchSpec.evmR mid := by
  have hAs : ArenaReady mid := hInv.1
  have hcode : mid.code = originalRuntimeCode := hAs.1.code
  obtain ⟨_, S, hInvAt⟩ := (evmInv_iff_at mid).1 hInv
  have hFW_all := hInvAt.2.2.2.2.1
  set e0 := globN mid "ev"
  set c0 := globN mid "cur_cont"
  have hev_eq : evw.toNat = e0 := by simp [e0, globN, hev]
  have hhead_mem : (e0, c0) ∈ evmChain mid := List.mem_cons_self
  have hhead_FW := hFW_all (e0, c0) hhead_mem
  obtain ⟨hb_e0, _, hb_l0, _⟩ := EvmStepLemmas.frameWF_bounds hAs.2 hhead_FW
  dsimp only at hb_e0 hb_l0
  have he0_words : WordsOK mid (e0, 280) := (hhead_FW.1 (e0, 280) (by simp)).2
  obtain ⟨L, hd_e88, hm_e88⟩ := he0_words.2.2 11 (by omega)
  have he88_bv : evw + 88 = BitVec.ofNat 64 ((e0, 280).1 + 8 * 11) := by
    apply BitVec.eq_of_toNat_eq
    have h88 : (88 : BitVec 64).toNat = 88 := rfl
    dsimp only
    rw [BitVec.toNat_add, hev_eq, h88, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd88 : mid.memaddrs (evw + 88) := by rw [he88_bv]; exact hd_e88
  have hmL : mid.memory (evw + 88) = .word L := by rw [he88_bv]; exact hm_e88
  have hL_eq : L.toNat = memW mid (e0 + 88) := by
    unfold memW
    have hb : BitVec.ofNat 64 (e0 + 88) = evw + 88 := he88_bv.symm
    rw [hb, hmL]
  have hL_words : WordsOK mid (memW mid (e0 + 88), 24) :=
    (hhead_FW.1 (memW mid (e0 + 88), 24) (by simp)).2
  obtain ⟨arr0, hd0_raw, hm0_raw⟩ := hL_words.2.2 0 (by omega)
  obtain ⟨n, hd8_raw, hm8_raw⟩ := hL_words.2.2 1 (by omega)
  obtain ⟨cap, hd16_raw, hm16_raw⟩ := hL_words.2.2 2 (by omega)
  have hL0_bv : L = BitVec.ofNat 64 ((memW mid (e0 + 88), 24).1 + 8 * 0) := by
    apply BitVec.eq_of_toNat_eq
    dsimp only
    rw [hL_eq, BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega)).symm
  have hL8_bv : L + 8 = BitVec.ofNat 64 ((memW mid (e0 + 88), 24).1 + 8 * 1) := by
    apply BitVec.eq_of_toNat_eq
    have h8 : (8 : BitVec 64).toNat = 8 := rfl
    dsimp only
    rw [BitVec.toNat_add, hL_eq, h8, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hL16_bv : L + 16 = BitVec.ofNat 64 ((memW mid (e0 + 88), 24).1 + 8 * 2) := by
    apply BitVec.eq_of_toNat_eq
    have h16 : (16 : BitVec 64).toNat = 16 := rfl
    dsimp only
    rw [BitVec.toNat_add, hL_eq, h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hd0 : mid.memaddrs L := by rw [hL0_bv]; exact hd0_raw
  have hd8 : mid.memaddrs (L + 8) := by rw [hL8_bv]; exact hd8_raw
  have hd16 : mid.memaddrs (L + 16) := by rw [hL16_bv]; exact hd16_raw
  have hma : mid.memory L = .word arr0 := by rw [hL0_bv]; exact hm0_raw
  have hmn : mid.memory (L + 8) = .word n := by rw [hL8_bv]; exact hm8_raw
  have hmc : mid.memory (L + 16) = .word cap := by rw [hL16_bv]; exact hm16_raw
  have harr0_eq : arr0.toNat = memW mid (memW mid (e0 + 88)) := by
    have hb : BitVec.ofNat 64 (memW mid (e0 + 88)) = L := hL0_bv.symm
    change arr0.toNat = match mid.memory (BitVec.ofNat 64 (memW mid (e0 + 88))) with
      | .word w => w.toNat
    rw [hb, hma]
  have hn_eq : n.toNat = memW mid (memW mid (e0 + 88) + 8) := by
    have hb : BitVec.ofNat 64 (memW mid (e0 + 88) + 8) = L + 8 := hL8_bv.symm
    change n.toNat = match mid.memory (BitVec.ofNat 64 (memW mid (e0 + 88) + 8)) with
      | .word w => w.toNat
    rw [hb, hmn]
  have hcap_eq : cap.toNat = memW mid (memW mid (e0 + 88) + 16) := by
    have hb : BitVec.ofNat 64 (memW mid (e0 + 88) + 16) = L + 16 := hL16_bv.symm
    change cap.toNat = match mid.memory (BitVec.ofNat 64 (memW mid (e0 + 88) + 16)) with
      | .word w => w.toNat
    rw [hb, hmc]
  obtain ⟨hc1, hle, hcap_hi, _, _, hfl_se⟩ := frameWF_logs_cap_bounds hAs.2 hhead_FW
  dsimp only at hc1 hle hcap_hi hfl_se
  have hse := R11Shards.scratchEnd_val
  have hhl := R11Shards.heapLimit_val
  have hss := R11Shards.scratchStart_val
  have hL_in := (hhead_FW.1 (memW mid (e0 + 88), 24) (by simp)).1
  have hL_lo : scratchStart ≤ L.toNat := by
    have hsp := le_trans hAs.2.2.2.1 hAs.2.2.2.2.1
    have h1 := hL_in.1
    omega
  have hLh : L.toNat + 24 ≤ globN mid "heap_ptr" ∨ heapLimit ≤ L.toNat := Or.inr (by omega)
  have hFO_pw := hInvAt.2.2.2.2.2.2.2.1
  have hch_eq : evmChain mid = (e0, c0) ::
      (if memW mid (c0 + 16) = 0 then [] else
        evmChainFrom mid maxChain (memW mid c0) (memW mid (c0 + 8))) := by
    simp only [evmChain, evmChainFrom, e0, c0]
  have hhead_pw : (frameObjects mid (e0, c0)).Pairwise Disj := by
    have hpw := hFO_pw
    rw [hch_eq, List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
    exact hpw.1
  have hLd_disj : Disj (memW mid (e0 + 88), 24) (frameLogs mid (e0, c0)) := by
    have hpw := hhead_pw
    unfold frameObjects at hpw
    rw [List.pairwise_append] at hpw
    have hp7 := hpw.1
    simp only [List.pairwise_cons] at hp7
    exact hp7.2.2.2.2.1 _ (by simp)
  have hLd : L.toNat + 24 ≤ arr0.toNat ∨ arr0.toNat + 8 * cap.toNat ≤ L.toNat := by
    unfold frameLogs Disj at hLd_disj
    dsimp only at hLd_disj
    rw [← hcap_eq, ← harr0_eq, ← hL_eq] at hLd_disj
    rcases hLd_disj with h | h | h | h
    · omega
    · omega
    · exact Or.inl h
    · exact Or.inr h
  -- Step into `transferAppendReturn = seq (call log_append [ev, log]) (return 0)`
  dsimp only [EvmEkFkPrologue.transferAppendReturn] at hres hstepTail ⊢
  rw [evaluateHOLFiniteState_seq_line780] at hres hstepTail ⊢
  rcases hc : evaluateHOLFiniteState mid
      (.call (some (none, none)) (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]) with ⟨cr, cmid⟩
  simp only [hc] at hres hstepTail ⊢
  cases cr with
  | some r =>
    obtain ⟨v, hv⟩ := hres
    simp only at hv
    exact False.elim (transfer_call0_no_return_r31 mid _ _ v (by rw [hc, Option.some.inj hv]))
  | none =>
    simp only [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact,
      sizeOfShapeWithContextHOL, show (1 : Nat) ≤ 32 from by decide, ↓reduceIte,
      emptyLocalsHOLFinite] at hstepTail ⊢
    -- Unpack `call0` to `log_append`:
    have hcall_none : (evaluateHOLFiniteState mid
        (.call (some (none, none)) (ofString "log_append")
          [.var .global (ofString "ev"), .var .local (ofString "log")])).1 = none := by rw [hc]
    obtain ⟨values, body, callee, ret, rv, cpost, hargs, hlk, hrun, hceval⟩ :=
      Wave8M19.Htab.call0_flow mid (ofString "log_append")
        [.var .global (ofString "ev"), .var .local (ofString "log")]
        (Or.inl hcall_none)
    rw [hc] at hceval
    injection hceval with _ hcmid_eq
    have hvals : values = [.val (.word evw), .val (.word logw)] := by
      simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hev, hl] at hargs
      exact hargs.symm
    subst hvals
    have hlook := pan_two_word_lookup mid.code.lookup (ofString "log_append")
      (ofString "e") (ofString "log")
      (sourceFnBody Guest.Software.guestFn_log_append) evw logw
      (by decide)
      (by rw [hcode]; exact lookup_log_append_r31)
    rw [hlook] at hlk
    simp only [Option.some.injEq, Prod.mk.injEq] at hlk
    obtain ⟨rfl, rfl, rfl⟩ := hlk
    let ent := callEntryStateHOLFinite mid
      ((HolFiniteMapExact.empty.update (ofString "e", ValueHOL.val (.word evw))).update
        (ofString "log", ValueHOL.val (.word logw)))
    have hent_A : ArenaReady ent :=
      ⟨guestInv_callEntry _ _ hAs.1, arenaOK_congr (s := mid) rfl hAs.2⟩
    have hent_e : ent.locals.lookup (ofString "e") = some (.val (.word evw)) := by
      have hne : ofString "log" ≠ ofString "e" := by decide
      simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hne, Ne.symm hne]
    have hent_lg : ent.locals.lookup (ofString "log") = some (.val (.word logw)) := by
      simp [ent, callEntryStateHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
    have hpost2 : LogAppendPost2 ent L arr0 n cap cpost :=
      Ret.apply (log_append_run2 ent evw L logw arr0 n cap hent_A hent_e hent_lg
        hd88 hmL hma hmn hmc hd0 hd8 hd16
        (by rw [hn_eq, hcap_eq]; exact hle)
        (by rw [hcap_eq]; omega)
        (by rw [harr0_eq, hcap_eq]; omega)
        (by rw [hL_eq]; exact hb_l0)
        hLd
        (by simpa [ent, callEntryStateHOLFinite, globN] using hLh)
        (by rw [hcap_eq]; exact hc1)) hrun
    obtain ⟨_, _, _, _, _, arr', cap', _, _, _, _, _, hbranch, _, hmem_frame⟩ := hpost2
    -- Show `evmR {cmid with locals := empty} = evmR mid`:
    refine evmR_eq_of_chain_and_words hstepTail.1.2.2.2 (fun ec hec => ?_)
    have hFW_ec := hFW_all ec hec
    obtain ⟨hb_ec, _, _, _⟩ := EvmStepLemmas.frameWF_bounds hAs.2 hFW_ec
    have hec_in := (hFW_ec.1 (ec.1, 280) (by simp)).1
    have hec_lo : scratchStart ≤ ec.1 := by
      have hsp := le_trans hAs.2.2.2.1 hAs.2.2.2.2.1
      have h1 := hec_in.1
      omega
    -- Disjointness of `(ec.1, 280)` from `(L, 24)` and `(arr', 8 * cap')`:
    have hec_disj_L : Disj (ec.1, 280) (L.toNat, 24) := by
      rw [hL_eq]
      by_cases heq_ec : ec = (e0, c0)
      · subst heq_ec
        have hpw := hhead_pw
        unfold frameObjects at hpw
        rw [List.pairwise_append] at hpw
        have hp7 := hpw.1
        simp only [List.pairwise_cons] at hp7
        exact hp7.1 _ (by simp)
      · have hpw := hFO_pw
        rw [hch_eq] at hec hpw
        rcases List.mem_cons.1 hec with rfl | hec_tl
        · exact absurd rfl heq_ec
        · simp only [List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
          exact R11Shards.Disj.symm (hpw.2.2 (memW mid (e0 + 88), 24)
            (by simp [frameObjects]) (ec.1, 280)
            (List.mem_flatten.2 ⟨frameObjects mid ec, List.mem_map.2 ⟨ec, hec_tl, rfl⟩,
              by simp [frameObjects]⟩))
    have hec_disj_arr' : Disj (ec.1, 280) (arr'.toNat, 8 * cap'.toNat) := by
      rcases hbranch with ⟨rfl, rfl⟩ | ⟨harr_lo, harr_hi, _⟩
      · rw [harr0_eq, hcap_eq]
        change Disj (ec.1, 280) (frameLogs mid (e0, c0))
        by_cases heq_ec : ec = (e0, c0)
        · subst heq_ec
          have hpw := hhead_pw
          unfold frameObjects at hpw
          rw [List.pairwise_append] at hpw
          have hp7 := hpw.1
          simp only [List.pairwise_cons] at hp7
          exact hp7.1 _ (by simp)
        · have hpw := hFO_pw
          rw [hch_eq] at hec hpw
          rcases List.mem_cons.1 hec with rfl | hec_tl
          · exact absurd rfl heq_ec
          · simp only [List.map_cons, List.flatten_cons, List.pairwise_append] at hpw
            exact R11Shards.Disj.symm (hpw.2.2 (frameLogs mid (e0, c0))
              (by simp [frameObjects]) (ec.1, 280)
              (List.mem_flatten.2 ⟨frameObjects mid ec, List.mem_map.2 ⟨ec, hec_tl, rfl⟩,
                by simp [frameObjects]⟩))
      · have hhp_cmid_lim :
            globN ({ cmid with locals := HolFiniteMapExact.empty } : PanSemStateFiniteExact 64 F) "heap_ptr" ≤
              heapLimit := hstepTail.1.1.1.2.2.1
        have hcpost_globals : cpost.globals = cmid.globals :=
          (congrArg PanSemStateFiniteExact.globals hcmid_eq).symm
        have hhp_post_lim : globN cpost "heap_ptr" ≤ heapLimit := by
          unfold globN at hhp_cmid_lim ⊢
          change (match cpost.globals.lookup (ofString "heap_ptr") with
            | some (.val (.word w)) => w.toNat | _ => 0) ≤ heapLimit
          rw [hcpost_globals]
          exact hhp_cmid_lim
        unfold Disj; dsimp only
        right; right; right
        omega
    have hcell_eq : ∀ k : Nat, (k = 64 ∨ k = 192) →
        memW ({ cmid with locals := HolFiniteMapExact.empty } : PanSemStateFiniteExact 64 F) (ec.1 + k) =
          memW mid (ec.1 + k) := by
      intro k hk
      have hk_le : k + 8 ≤ 280 := by rcases hk with rfl | rfl <;> decide
      let addr := BitVec.ofNat 64 (ec.1 + k)
      have haddr_nat : addr.toNat = ec.1 + k := by
        dsimp only [addr]
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      have hno_arr : ¬ CellHits addr.toNat (arr'.toNat, 8 * cap'.toNat) := by
        intro hhit
        unfold CellHits at hhit
        rw [haddr_nat] at hhit
        unfold Disj at hec_disj_arr'; dsimp only at hec_disj_arr'
        rcases hec_disj_arr' with h | h | h | h <;> omega
      have hne_L : ∀ off : Nat, off ≤ 16 → addr ≠ L + BitVec.ofNat 64 off := by
        intro off hoff heq
        have hto := congrArg BitVec.toNat heq
        have hoff_nat : (BitVec.ofNat 64 off).toNat = off := by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
        rw [haddr_nat, BitVec.toNat_add, hoff_nat, Nat.mod_eq_of_lt (by omega)] at hto
        unfold Disj at hec_disj_L; dsimp only at hec_disj_L
        rcases hec_disj_L with h | h | h | h <;> omega
      have hne0 : addr ≠ L := by
        intro heq; exact hne_L 0 (by omega) (by simpa using heq)
      have hne8 : addr ≠ L + 8 := hne_L 8 (by omega)
      have hne16 : addr ≠ L + 16 := hne_L 16 (by omega)
      have hm_eq := hmem_frame addr hno_arr hne0 hne8 hne16
      unfold memW
      have hcmid_mem : cmid.memory = cpost.memory := by
        have h := congrArg PanSemStateFiniteExact.memory hcmid_eq
        exact h
      change (match cmid.memory (BitVec.ofNat 64 (ec.1 + k)) with | .word w => w.toNat) =
        (match mid.memory (BitVec.ofNat 64 (ec.1 + k)) with | .word w => w.toNat)
      rw [hcmid_mem]
      exact congrArg (fun v => match v with | .word w => w.toNat) hm_eq
    exact ⟨hcell_eq 64 (Or.inl rfl), hcell_eq 192 (Or.inr rfl)⟩

private theorem transfer_log_tail_evmR_eq_r31 {F : Type}
    (mid0 : PanSemStateFiniteExact 64 F) (p sysw topic sender recipient evw : BitVec 64)
    (av : ValueHOL 64) (inv0 : EvmInv mid0)
    (hp0 : mid0.globals.lookup (ofString "heap_ptr") = some (.val (.word p)))
    (hsysw0 : mid0.globals.lookup (ofString "vm_system_address") = some (.val (.word sysw)))
    (htopic0 : mid0.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hs0 : mid0.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hr0 : mid0.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (ha0 : mid0.locals.lookup (ofString "amount") = some av)
    (hev0 : mid0.globals.lookup (ofString "ev") = some (.val (.word evw)))
    (ready0 : Inside (globN mid0 "vm_system_address", 20) sourceBase (globN mid0 "heap_ptr"))
    (hr : Resumes (evaluateHOLFiniteState mid0 EvmEkFkPrologue.transferLogTail).1) :
    OpDispatchSpec.evmR (evaluateHOLFiniteState mid0 EvmEkFkPrologue.transferLogTail).2 =
      OpDispatchSpec.evmR mid0 := by
  obtain ⟨mid1, hl1, heap1, addr1, words1, step1, resum1, er1, es1, be1, loc1, out1, bytes1⟩ :=
    EvmEkFkPrologue.transfer_alloc_log_address_prefix mid0 p sysw _ inv0 hp0 hsysw0 hr
  obtain ⟨topicsw, htop1⟩ : ∃ topicsw : BitVec 64,
      mid1.globals.lookup (ofString "heap_ptr") = some (.val (.word topicsw)) :=
    globalWord_of_globN_pos mid1 "heap_ptr"
      (by have h := step1.1.1.1.2.1; rw [EvmBase.sourceBase_val] at h; omega)
  have g1 (name : String) (hn : ofString name ≠ ofString "heap_ptr") :
      mid1.globals.lookup (ofString name) = mid0.globals.lookup (ofString name) :=
    (step1.1.2.2.1 _ (by simpa using hn)).symm
  have hin1 : Inside (p.toNat, 40) (globN mid0 "heap_ptr") (globN mid1 "heap_ptr") :=
    ⟨by simp [globN, hp0], by rw [heap1]⟩
  obtain ⟨mid2, ht2, heap2, step2, be2, words2, addr2, tp2, tn2, loc2, out2, bytes2, resum2, er2, es2⟩ :=
    EvmEkFkPrologue.transfer_accumulated_topics_record_prefix mid0 mid1 topicsw topic sender recipient p
      EvmEkFkPrologue.transferDataTail
      inv0 step1 be1 out1 bytes1 htop1 ((g1 _ (by decide)).trans htopic0)
      ((loc1 _ (by decide)).trans hs0) ((loc1 _ (by decide)).trans hr0)
      hl1 words1 hin1 resum1
  obtain ⟨dataw, hd2⟩ : ∃ dataw : BitVec 64,
      mid2.globals.lookup (ofString "heap_ptr") = some (.val (.word dataw)) :=
    globalWord_of_globN_pos mid2 "heap_ptr"
      (by have h := step2.1.1.1.2.1; rw [EvmBase.sourceBase_val] at h; omega)
  have g2 (name : String) (hn : ofString name ≠ ofString "heap_ptr") :
      mid2.globals.lookup (ofString name) = mid0.globals.lookup (ofString name) :=
    (step2.1.2.2.1 _ (by simpa using hn)).symm
  have gp1 : globN mid1 "heap_ptr" = topicsw.toNat := by simp [globN, htop1]
  have hin2 : Inside (p.toNat, 40) (globN mid0 "heap_ptr") (globN mid2 "heap_ptr") :=
    ⟨hin1.1, by rw [heap2]; have h := hin1.2; rw [gp1] at h; omega⟩
  obtain ⟨mid3, hd3, hl3, heap3, step3, ev3, sys3, words3, dp3, dn3, frame3, be3, out3, bytes3, resum3, er3, es3⟩ :=
    EvmEkFkPrologue.transfer_alloc_data_record_prefix mid0 mid2 dataw p av
      EvmEkFkPrologue.transferAppendReturn
      inv0 step2 be2 out2 bytes2
      ((loc2 _ (by decide)).trans ((loc1 _ (by decide)).trans ha0))
      ((loc2 _ (by decide)).trans hl1) words2 hin2 hd2 resum2
  have hR3 : OpDispatchSpec.evmR mid3 = OpDispatchSpec.evmR mid0 :=
    evmR_of_accumulated_frame_r31 inv0 step3 be3 out3 bytes3
  have hdata2 : dataw.toNat = globN mid2 "heap_ptr" := by simp [globN, hd2]
  have hmono23 : globN mid2 "heap_ptr" ≤ globN mid3 "heap_ptr" := by
    rw [← hdata2, heap3]; omega
  have hbound_log : p.toNat + 40 < 2 ^ 64 := by
    have h := hin2.2; rw [← hdata2] at h; have h64 := dataw.isLt; omega
  have sys20 : globN mid2 "vm_system_address" = globN mid0 "vm_system_address" := by
    unfold globN; rw [g2 "vm_system_address" (by decide)]
  have sys10 : globN mid1 "vm_system_address" = globN mid0 "vm_system_address" := by
    unfold globN; rw [g1 "vm_system_address" (by decide)]
  have addr3 : memW mid3 p.toNat = globN mid3 "vm_system_address" := by
    rw [frame3 _ (by omega) (by omega) (by omega) (by omega), addr2, addr1, sys3, sys20, sys10]
  have tp3 : memW mid3 (p.toNat + 8) = topicsw.toNat := by
    rw [frame3 _ (by omega) (by omega) (by omega) (by omega), tp2]
  have tn3 : memW mid3 (p.toNat + 16) = 3 := by
    rw [frame3 _ (by omega) (by omega) (by omega) (by omega), tn2]
  have htop_in2 : Inside (topicsw.toNat, 96) (globN mid0 "heap_ptr") (globN mid2 "heap_ptr") :=
    ⟨by rw [← gp1]; exact step1.1.2.1, by rw [heap2]⟩
  obtain ⟨_, S0, invAt0⟩ := (evmInv_iff_at mid0).1 inv0
  obtain ⟨Nd0, tries0, avoids0⟩ := invAt0.2.2.2.2.2.2.2.2.2.1
  obtain ⟨invAt3, tries3, avoids3⟩ := EvmEkFkPrologue.transfer_fixed_witness_of_accumulated_frame
    inv0 invAt0 tries0 avoids0 step3 be3 out3 bytes3
  have hdisj3 : ∀ x ∈ [(p.toNat, 40), (topicsw.toNat, 96), (dataw.toNat, 32)],
      (∀ t ∈ S0, ∀ i ∈ htabFootprint mid3 t, Disj x i) ∧
      (∀ j ∈ fixedObjects mid3, Disj x j) ∧
      (∀ ec ∈ evmChain mid3, ∀ o ∈ frameObjects mid3 ec, Disj x o) ∧
      (∀ j ∈ nodeExtents mid3 Nd0, Disj x j) ∧
      (∀ ec ∈ evmChain mid3, Disj x (memW mid3 (ec.1 + 112), 176)) := by
    intro x hx
    apply EvmEkFkPrologue.transfer_fresh_fixed_disjoint_of_accumulated_frame inv0 step3
      ⟨invAt0.1.1, invAt0.1.2.1, invAt0.1.2.2.1, tries0⟩ be3 out3 bytes3
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨hin2.1, le_trans hin2.2 hmono23⟩
    · exact ⟨htop_in2.1, le_trans htop_in2.2 hmono23⟩
    · exact ⟨by rw [hdata2]; exact step2.1.2.1, by rw [heap3]⟩
  have hev3 : mid3.globals.lookup (ofString "ev") = some (.val (.word evw)) :=
    ev3.trans ((g2 "ev" (by decide)).trans hev0)
  have hres_tail := EvmEkFkPrologue.transfer_log_append_tail_resumes_returned mid3 step3.1.1.1.1.code resum3
  have hstepTail : EvmEkFkPrologue.EvmStepCC ["heap_ptr"] mid3
      (evaluateHOLFiniteState mid3 EvmEkFkPrologue.transferAppendReturn).2 :=
    EvmEkFkPrologue.transfer_log_append_tail_step_at mid3 evw p topicsw.toNat dataw.toNat
      S0 Nd0 invAt3 tries3 avoids3 step3.1.1
      (by simp [globN, hev3]) words3
      ⟨le_trans inv0.1.2.1 hin2.1, le_trans hin2.2 hmono23⟩
      ⟨by rw [sys3, sys20]; exact ready0.1,
       by rw [sys3, sys20]; exact le_trans ready0.2 (le_trans step2.1.2.1 hmono23)⟩
      ⟨le_trans inv0.1.2.1 htop_in2.1, le_trans htop_in2.2 hmono23⟩
      ⟨by rw [hdata2]; exact le_trans inv0.1.2.1 step2.1.2.1, by rw [heap3]⟩
      addr3 tp3 tn3 dp3 dn3
      (by have h := hin1.2; omega)
      (by rw [hdata2, heap2])
      (by rw [EvmEkFkPrologue.logOwnedIvls_of_transfer addr3 tp3 tn3 dp3 dn3]; exact hdisj3)
      (by simpa only [evalHOLExact] using hev3)
      (by simpa only [evalHOLExact] using hl3)
      hres_tail
  have hR_tail : OpDispatchSpec.evmR (evaluateHOLFiniteState mid3 EvmEkFkPrologue.transferAppendReturn).2 =
      OpDispatchSpec.evmR mid3 :=
    log_append_tail_evmR_eq_r31 mid3 evw p step3.1.1 hev3 hl3 hstepTail hres_tail
  have hloc_free : ∀ (t : PanSemStateFiniteExact 64 F) L,
      OpDispatchSpec.evmR ({ t with locals := L } : PanSemStateFiniteExact 64 F) =
        OpDispatchSpec.evmR t := fun t L =>
    evmR_eq_of_chain_and_words (evmChain_with_locals t L t.clock) (fun _ _ => ⟨rfl, rfl⟩)
  have hpost1 : (evaluateHOLFiniteState mid0 EvmEkFkPrologue.transferLogTail).2 =
      { (evaluateHOLFiniteState mid1
          (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
            (EvmEkFkPrologue.transferTopicWrites
              (EvmEkFkPrologue.transferRecordPairWrites 8 (ofString "topics") 3
                EvmEkFkPrologue.transferDataTail)))).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState mid1
            (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
              (EvmEkFkPrologue.transferTopicWrites
                (EvmEkFkPrologue.transferRecordPairWrites 8 (ofString "topics") 3
                  EvmEkFkPrologue.transferDataTail)))).2.locals
          (ofString "log", mid0.locals.lookup (ofString "log")) } := es1
  have hpost2 : (evaluateHOLFiniteState mid1
      (.decCall (ofString "topics") .one (ofString "alloc") [.const 96]
        (EvmEkFkPrologue.transferTopicWrites
          (EvmEkFkPrologue.transferRecordPairWrites 8 (ofString "topics") 3
            EvmEkFkPrologue.transferDataTail)))).2 =
      { (evaluateHOLFiniteState mid2 EvmEkFkPrologue.transferDataTail).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState mid2 EvmEkFkPrologue.transferDataTail).2.locals
          (ofString "topics", mid1.locals.lookup (ofString "topics")) } := es2
  have hpost3 : (evaluateHOLFiniteState mid2 EvmEkFkPrologue.transferDataTail).2 =
      { (evaluateHOLFiniteState mid3 EvmEkFkPrologue.transferAppendReturn).2 with
        locals := HolFiniteMapExact.resVarEq
          (evaluateHOLFiniteState mid3 EvmEkFkPrologue.transferAppendReturn).2.locals
          (ofString "data", mid2.locals.lookup (ofString "data")) } := es3
  rw [hpost1, hloc_free, hpost2, hloc_free, hpost3, hloc_free, hR_tail, hR3]

theorem emit_transfer_log_body_step_eqR_r31 {F : Type}
    (s : PanSemStateFiniteExact 64 F) (sender recipient topic : BitVec 64) (av : ValueHOL 64)
    (hInv : EvmInv s)
    (hsys : Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (htopic : s.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)))
    (hsender : s.locals.lookup (ofString "sender") = some (.val (.word sender)))
    (hrecipient : s.locals.lookup (ofString "recipient") = some (.val (.word recipient)))
    (ha : s.locals.lookup (ofString "amount") = some av)
    (hr : Resumes (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).1) :
    EvmStepCC ["heap_ptr"] s
      (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).2 ∧
    OpDispatchSpec.evmR (evaluateHOLFiniteState s (sourceFnBody Guest.Software.guestFn_emit_transfer_log)).2 =
      OpDispatchSpec.evmR s := by
  have hst_full := EvmEkFkPrologue.emit_transfer_log_body_step s sender recipient topic av
    hInv hsys htopic hsender hrecipient ha hr
  refine ⟨⟨hst_full.1, hst_full.2⟩, ?_⟩
  have hloc_free : ∀ (t : PanSemStateFiniteExact 64 F) L,
      OpDispatchSpec.evmR ({ t with locals := L } : PanSemStateFiniteExact 64 F) =
        OpDispatchSpec.evmR t := fun t L =>
    evmR_eq_of_chain_and_words (evmChain_with_locals t L t.clock) (fun _ _ => ⟨rfl, rfl⟩)
  have body : sourceFnBody Guest.Software.guestFn_emit_transfer_log =
      .decCall (ofString "z") .one (ofString "u256_is_zero") [.var .local (ofString "amount")]
        (.seq (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0))
          (.return (.const 0)) .skip) EvmEkFkPrologue.transferLogTail) := rfl
  rw [body] at hr ⊢
  obtain ⟨params_z, body_z, ret_z, lookup_z, spec_z⟩ := EvmFrameSpecs.ro_u256_is_zero
  have hcode := hInv.1.1.code
  rw [evaluateHOLFiniteState_decCall_fixClockRewrite] at hr ⊢
  rcases ha_ev : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "amount")] with _ | vals_z
  · simp only [ha_ev] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  simp only [ha_ev] at hr ⊢
  rcases hl_z : lookupCodeHOLFinite s.code.lookup (ofString "u256_is_zero") vals_z with _ | ⟨body_z', callee_z, ret_z'⟩
  · simp only [hl_z] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  simp only [hl_z] at hr ⊢
  by_cases hz_clk : s.clock = 0
  · simp only [hz_clk, ↓reduceIte] at hr; rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  simp only [hz_clk, ↓reduceIte] at hr ⊢
  have hb_z := lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_is_zero")
    params_z body_z body_z' ret_z ret_z' vals_z callee_z (by rw [hcode]; exact lookup_z) hl_z
  subst hb_z
  have entry_z : callEntryStateHOLFinite s callee_z =
      {s with locals := callee_z, clock := (callEntryStateHOLFinite s callee_z).clock} := by cases s; rfl
  have hex_z : ∃ vs, lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "u256_is_zero") vs =
      some (body_z', (callEntryStateHOLFinite s callee_z).locals, ret_z) := by
    have he_z := lookupCodeHOLFinite_installed_return s (ofString "u256_is_zero")
      params_z body_z' body_z' ret_z ret_z' vals_z callee_z (by rw [hcode]; exact lookup_z) hl_z
    subst he_z
    exact ⟨vals_z, by simpa only [hcode, callEntryStateHOLFinite] using hl_z⟩
  rcases run_z : evaluateHOLFiniteState (callEntryStateHOLFinite s callee_z) body_z' with ⟨res_z, post_z⟩
  simp only [run_z] at hr ⊢
  cases res_z with
  | none => rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
  | some rz =>
    cases rz with
    | exception ez vz =>
      have ro_z := spec_z (callEntryStateHOLFinite s callee_z) hcode
        (guestInv_callEntry s callee_z hInv.1.1) hex_z (by rw [run_z]; simp) (by rw [run_z]; exact hr)
      rw [run_z] at ro_z
      have postEq := R13.state_trans_locals_clock entry_z ro_z
      have eq_post : emptyLocalsHOLFinite post_z =
          {s with locals := (emptyLocalsHOLFinite post_z).locals,
                  clock := (emptyLocalsHOLFinite post_z).clock} := by
        have h : emptyLocalsHOLFinite post_z =
            {post_z with locals := (emptyLocalsHOLFinite post_z).locals, clock := post_z.clock} := by
          cases post_z; rfl
        exact R13.state_trans_locals_clock postEq h
      dsimp only
      rw [eq_post]
      exact evmR_eq_of_chain_and_words (evmChain_with_locals _ _ _) (fun _ _ => ⟨rfl, rfl⟩)
    | returned vz =>
      dsimp only at hr ⊢
      split at hr
      · rename_i hs_z
        simp only [hs_z, ↓reduceIte]
        have ro_z := spec_z (callEntryStateHOLFinite s callee_z) hcode
          (guestInv_callEntry s callee_z hInv.1.1) hex_z (by rw [run_z]; simp)
          (by rw [run_z]; exact Or.inl ⟨vz, rfl⟩)
        rw [run_z] at ro_z
        have postEq := R13.state_trans_locals_clock entry_z ro_z
        let mid0 := setVarHOLFinite (ofString "z") vz {post_z with locals := s.locals}
        have mid0_eq : mid0 = {s with locals := mid0.locals, clock := mid0.clock} := by
          have h : mid0 = {post_z with locals := mid0.locals, clock := post_z.clock} := by
            cases post_z; rfl
          exact R13.state_trans_locals_clock postEq h
        have loc0 : ∀ k, k ≠ ofString "z" → mid0.locals.lookup k = s.locals.lookup k := by
          intro k hk
          simp [mid0, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
        have inv0 : EvmInv mid0 := by rw [mid0_eq]; exact localsFree_evmInv _ _ _ hInv
        have hR0 : OpDispatchSpec.evmR mid0 = OpDispatchSpec.evmR s := by
          rw [mid0_eq]
          exact evmR_eq_of_chain_and_words (evmChain_with_locals _ _ _) (fun _ _ => ⟨rfl, rfl⟩)
        rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite] at hr ⊢
        split at hr
        · rename_i wz hwz
          split at hr
          · rename_i hzw0
            simp only [hwz, hzw0, ↓reduceIte, evaluateHOLFiniteState_skip] at hr ⊢
            obtain ⟨p, hp0⟩ : ∃ p : BitVec 64, mid0.globals.lookup (ofString "heap_ptr") = some (.val (.word p)) :=
              globalWord_of_globN_pos mid0 "heap_ptr"
                (by have h := inv0.1.2.1; rw [EvmBase.sourceBase_val] at h; omega)
            have ready0 : Inside (globN mid0 "vm_system_address", 20) sourceBase (globN mid0 "heap_ptr") := by
              rw [mid0_eq]; exact hsys
            obtain ⟨sysw, hsysw0⟩ : ∃ w : BitVec 64,
                mid0.globals.lookup (ofString "vm_system_address") = some (.val (.word w)) :=
              globalWord_of_globN_pos mid0 "vm_system_address"
                (by have h := ready0.1; rw [EvmBase.sourceBase_val] at h; omega)
            have htopic0 : mid0.globals.lookup (ofString "transfer_topic") = some (.val (.word topic)) := by
              rw [mid0_eq]; exact htopic
            obtain ⟨evw, hev0⟩ : ∃ w : BitVec 64, mid0.globals.lookup (ofString "ev") = some (.val (.word w)) :=
              globalWord_of_globN_pos mid0 "ev" (by
                obtain ⟨_, S, invAt⟩ := (evmInv_iff_at mid0).1 inv0
                have fw := invAt.2.2.2.2.1 (globN mid0 "ev", globN mid0 "cur_cont") List.mem_cons_self
                have hlo := (fw.1 (globN mid0 "ev", 280) (by simp)).1.1
                have hgap := inv0.1.2.2.2.1
                have hsp := inv0.1.2.2.2.2.1
                rw [R11Shards.scratchStart_val] at hgap
                omega)
            have hR_log := transfer_log_tail_evmR_eq_r31 mid0 p sysw topic sender recipient evw av
              inv0 hp0 hsysw0 htopic0
              ((loc0 _ (by decide)).trans hsender)
              ((loc0 _ (by decide)).trans hrecipient)
              ((loc0 _ (by decide)).trans ha)
              hev0 ready0 hr
            change OpDispatchSpec.evmR
              { (evaluateHOLFiniteState mid0 EvmEkFkPrologue.transferLogTail).2 with
                locals := HolFiniteMapExact.resVarEq
                  (evaluateHOLFiniteState mid0 EvmEkFkPrologue.transferLogTail).2.locals
                  (ofString "z", s.locals.lookup (ofString "z")) } = OpDispatchSpec.evmR s
            rw [hloc_free, hR_log, hR0]
          · rename_i hzw_ne0
            simp only [hwz, hzw_ne0, ↓reduceIte, evaluateHOLFiniteState_return, evalHOLExact,
              shapeOfHOLExact, sizeOfShapeWithContextHOL, show (1 : Nat) ≤ 32 from by decide,
              ↓reduceIte, emptyLocalsHOLFinite] at hr ⊢
            change OpDispatchSpec.evmR
              { { mid0 with locals := HolFiniteMapExact.empty } with
                locals := HolFiniteMapExact.resVarEq
                  ({ mid0 with locals := HolFiniteMapExact.empty } : PanSemStateFiniteExact 64 F).locals
                  (ofString "z", s.locals.lookup (ofString "z")) } = OpDispatchSpec.evmR s
            rw [hloc_free, hloc_free, hR0]
        · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
      · rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h
    | _ => rcases hr with ⟨_, h⟩ | ⟨_, _, h, _⟩ <;> cases h

theorem evmStepCCEqR_emit_transfer_log_r31
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    EvmStepCCEqRSpec (fun _ => True) ["heap_ptr"] (ofString "emit_transfer_log") := by
  refine ⟨_, _, _, lookup_emit_transfer_log_r31, ?_⟩
  intro F s hcode ⟨hInv, _⟩ hex hnt hr
  obtain ⟨sender, recipient, amount, hs, hrp, ha⟩ := emit_transfer_log_params_r31 hex
  obtain ⟨topic, htopic⟩ := hInv.1.2.2.2.2.2.2.2.2.2 "transfer_topic" (by decide)
  exact emit_transfer_log_body_step_eqR_r31 s sender recipient topic amount
    hInv (hsys s hInv) htopic hs hrp ha hr

private theorem hp_sub_hp_sp_r31 :
    ∀ g ∈ (["heap_ptr"] : List String), g ∈ (["heap_ptr", "scratch_ptr"] : List String) := by
  intro g hg
  simp at hg ⊢
  exact Or.inl hg

theorem eps_emit_transfer_log_r31
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "emit_transfer_log") :=
  eps_of_evmStepCCEqR_r31 hp_sub_hp_sp_r31 (evmStepCCEqR_emit_transfer_log_r31 hsys)

theorem epsA_emit_transfer_log_r31
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr")) :
    EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr"] s post ∧ OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "emit_transfer_log") :=
  epsA_of_evmStepCCEqR_r31 (by decide) (by decide) hp_sub_hp_sp_r31 (evmStepCCEqR_emit_transfer_log_r31 hsys)

/-! ## 5. Assembled `WorldAccountSpecs`, `WorldAccountSpecsA`, and `WorldAccountSpecsCall_g10` -/

theorem worldAccountSpecs_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (hset : EvmPreservingSpec (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")) :
    WorldAccountSpecs where
  eps_get_account := eps_get_account_r31
  eps_ext_code_of := eps_ext_code_of_r31
  eps_get_storage := eps_get_storage_r31 hdb
  eps_get_storage_original := eps_get_storage_original_r31 hdb
  eps_set_storage := hset
  eps_is_account_alive := eps_is_account_alive_r31
  eps_move_ether := eps_move_ether_r31
  eps_emit_transfer_log := eps_emit_transfer_log_r31 hsys

theorem worldAccountSpecsA_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (hsetA : EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")) :
    WorldAccountSpecsA where
  epsA_get_account := epsA_get_account_r31
  epsA_ext_code_of := epsA_ext_code_of_r31
  epsA_get_storage := epsA_get_storage_r31 hdb
  epsA_get_storage_original := epsA_get_storage_original_r31 hdb
  epsA_set_storage := hsetA
  epsA_is_account_alive := epsA_is_account_alive_r31
  epsA_move_ether := epsA_move_ether_r31
  epsA_emit_transfer_log := epsA_emit_transfer_log_r31 hsys

theorem worldAccountSpecsCall_g10_r31
    (hdb : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → StorageCreateFinish.WitnessDbOK s)
    (hsys : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F),
      EvmInv s → Inside (globN s "vm_system_address", 20) sourceBase (globN s "heap_ptr"))
    (hsetA : EvmPreservingSpecA (fun _ => True)
      (fun s _ post => GlobalsKept ["heap_ptr", "scratch_ptr", "journal", "journal_n", "journal_cap"] s post ∧
        OpDispatchSpec.evmR post = OpDispatchSpec.evmR s)
      (ofString "set_storage")) :
    WorldAccountSpecsCall_g10 :=
  { toWorldAccountSpecsA := worldAccountSpecsA_r31 hdb hsys hsetA
    epsA_is_account_alive_k32 := epsA_is_account_alive_k32_r31 }

end InitECandidate.Solver.Wave8GuestInv.ContractParts
