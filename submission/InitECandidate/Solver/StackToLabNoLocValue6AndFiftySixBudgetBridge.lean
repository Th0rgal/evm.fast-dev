import InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6
import InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster
import InitECandidate.Solver.WitnessDagMemoizationAndSubcallRevertBridge

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# StackToLabNoLocValue6AndFiftySixBudgetBridge

Wave 5 bridge (W5_161). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.StackToLabNoLocValue6AndFiftySixBudgetBridge

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6
open InitECandidate.Solver.WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster
open InitECandidate.Solver.WitnessDagMemoizationAndSubcallRevertBridge
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. After LabToTarget, every section is a stub or has no jump, jumpCmp, call or locValue
into section 6. -/
theorem panToTarget_noStubJumpOrLocValue_bridge_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    (∀ s' ∈ L',
      InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
      ∀ x ∈ s'.lines, JumpOk x = true) ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.locValue 3 (.lab 64 1)) (0 : BitVec width) [] 0) = true :=
  ⟨fun s' hs => panToTarget_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp off
      ic pos labs ffis L' labs' h s' hs,
   jumpOk_rejects_stub_jump, jumpOk_rejects_stub_locValue, jumpOk_accepts_user_locValue⟩

/-- 2. The same for user sections only: none reaches section 6. -/
theorem panToTarget_user_sections_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    (∀ s' ∈ L',
      InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
      ∀ x ∈ s'.lines, JumpOk x = true) ∧
    JC (.locValue 0 storeConstsStubLocation 0 : HolProg width) = false :=
  ⟨fun s' hs hu => panToTarget_user_sections_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp
      off ic pos labs ffis L' labs' h s' hs hu,
   jc_rejects_locValue_stub⟩

/-- 3. Word-level rejection: a locValue into section 6 and a return into section 6 are rejected,
while a user call is accepted. -/
theorem word_level_section6_rejection_non_vacuous_and_tight :
    (NSL (WordLangProgHOL.locValue (α := BitVec width) 0 storeConstsStubLocation) = false) ∧
    (NSL (WordLangProgHOL.call (α := BitVec width)
        (some ([], (.ln, .ln), .skip, storeConstsStubLocation, 0)) (some 64) [] none) = false) ∧
    (NSL (WordLangProgHOL.call (α := BitVec width)
        (some ([], (.ln, .ln), .locValue 1 64, 64, 0)) (some 64) [] none) = true) :=
  ⟨nsl_rejects_locValue_stub, nsl_rejects_return_into_stub, nsl_accepts_user⟩

/-- 4. Heap floors and the heap cap: leaf ≥ 98, extension ≥ 90, branch ≥ 448 bytes,
at most 345_470_831 nodes. -/
theorem heap_floors_and_node_cap_non_vacuous_and_tight (L E B : Nat)
    (h : InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf L E B ≤
      InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapAvail) :
    InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf 1 0 0 = 98 ∧
    InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf 0 1 0 = 90 ∧
    InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.heapOf 0 0 1 = 448 ∧
    L + E + B ≤ 345470831 :=
  ⟨node_heap_floors_non_vacuous_and_tight.1,
   node_heap_floors_non_vacuous_and_tight.2.1,
   node_heap_floors_non_vacuous_and_tight.2.2.1,
   (nodes_by_heap_cap_non_vacuous_and_tight L E B h).1⟩

/-- 5. Yukon thresholds: tau ≤ 28 at 1x, tau ≤ 5 at 5x. -/
theorem heap_rate_thresholds_non_vacuous_and_tight :
    28 * 31092374808 < yukon ∧ yukon < 29 * 31092374808 ∧
    5 * (5 * 31092374808) < yukon ∧ yukon < 5 * (6 * 31092374808) :=
  ⟨heap_thresholds_non_vacuous_and_tight.1.1, heap_thresholds_non_vacuous_and_tight.1.2,
   heap_thresholds_non_vacuous_and_tight.2.1, heap_thresholds_non_vacuous_and_tight.2.2⟩

/-- 6. DAG memoization: at most 33_554_428 nodes, 15_300_819_168 heap bytes, tau ≤ 58. -/
theorem memo_bound_non_vacuous_and_tight (L E B n : Nat)
    (hn : 4 * n ≤ 134217712) (h : L + E + B ≤ n) :
    L + E + B ≤ 33554428 ∧
    448 * 33554428 + 2 * 134217712 = 15300819168 ∧
    58 * 15300819168 < yukon ∧ yukon < 59 * 15300819168 :=
  ⟨(memo_nodes_heap_and_threshold_non_vacuous_and_tight L E B n hn h).1,
   (memo_nodes_heap_and_threshold_non_vacuous_and_tight L E B n hn h).2.1,
   (memo_nodes_heap_and_threshold_non_vacuous_and_tight L E B n hn h).2.2.2.1,
   (memo_nodes_heap_and_threshold_non_vacuous_and_tight L E B n hn h).2.2.2.2⟩

/-- 7. Combined MPT + nodedb + ts+64 envelope: 176_125_863_653, and 5x = 880_629_318_265
stays under Yukon with margin 20_090_607_209. -/
theorem mpt_nodedb_five_times_non_vacuous_and_tight :
    InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
    5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
    yukon - 5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint =
      20090607209 ∧
    5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint < yukon :=
  ⟨mpt_nodedb_joint_five_times_non_vacuous_and_tight.2.1,
   mpt_nodedb_joint_five_times_non_vacuous_and_tight.2.2.1,
   mpt_nodedb_joint_five_times_non_vacuous_and_tight.2.2.2,
   Nat.lt_of_sub_ne_zero
     (mpt_nodedb_joint_five_times_non_vacuous_and_tight.2.2.2 ▸ (by decide : 20090607209 ≠ 0))⟩

/-- 8. The 56-budget portfolio is strictly increasing and every budget is under Yukon
900_719_925_474. -/
theorem fifty_six_portfolio_under_yukon_non_vacuous_and_tight :
    FiftySixShape ∧ ClaimPayloads ∧ yukon = 900719925474 :=
  ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight, rfl⟩

/-- 9. Every one of the 56 budgets carries a finite certificate, from one base certificate. -/
theorem fifty_six_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    FiftySixShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨portfolio_non_vacuous_and_tight, certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand bridge: section-6 inaccessibility after LabToTarget, memoized heap bound,
5x MPT+nodedb envelope, and the 56-budget portfolio under Yukon. -/
theorem stack_to_lab_no_loc_value6_and_fifty_six_budget_bridge_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (cert : CertificateAt 1212035192) :
    (∀ s' ∈ L',
      InitECandidate.Solver.PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false →
      ∀ x ∈ s'.lines, JumpOk x = true) ∧
    JumpOk (.labAsm (.locValue 3 (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    (448 * 33554428 + 2 * 134217712 = 15300819168 ∧ 58 * 15300819168 < yukon) ∧
    (InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
      5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
      5 * InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge.joint < yukon) ∧
    (FiftySixShape ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨fun s' hs hu => panToTarget_user_sections_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp
      off ic pos labs ffis L' labs' h s' hs hu,
   jumpOk_rejects_stub_locValue,
   ⟨InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.memo_heap.1,
    InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound.memo_threshold.1⟩,
   ⟨mpt_nodedb_joint_five_times_non_vacuous_and_tight.2.1,
    mpt_nodedb_joint_five_times_non_vacuous_and_tight.2.2.1,
    Nat.lt_of_sub_ne_zero
      (mpt_nodedb_joint_five_times_non_vacuous_and_tight.2.2.2 ▸ (by decide : 20090607209 ≠ 0))⟩,
   ⟨portfolio_non_vacuous_and_tight, certificates_non_vacuous_and_tight cert⟩⟩

end InitECandidate.Solver.StackToLabNoLocValue6AndFiftySixBudgetBridge
