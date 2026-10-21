import InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
import InitECandidate.Solver.StackToLabNoLocValue6AndFiftySixBudgetBridge
import InitECandidate.Solver.GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_167. Exact decode arithmetic in the imported tick model, compiler section safety,
and sixty conditional finite budgets. No unconditional execution certificate is asserted. -/
namespace InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster

open InitECandidate.Solver
open _root_.InitECandidate.Solver.GuestWitnessDecodeExactTicksPerByteAudit
open _root_.InitECandidate.Solver.GuestWitnessDagMemoizationAndHeapBound (heapOf heapAvail)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)
open _root_.InitECandidate.Solver.YukonVerifyScriptAudit (validFiniteClaim)

abbrev Previous := GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster.portfolio

def portfolio : List Nat := Previous ++ [880629318269, 880629318270]

def sixtyClaims : List (Nat × String) :=
  GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster.fiftyEightClaims ++
  [(880629318269, "{\"K\":880629318269}"),
   (880629318270, "{\"K\":880629318270}")]

def ExactTicks : Prop :=
  tLeaf = 43 ∧ tExt = 48 ∧ tBranch = 326 ∧
  heapOf 1 0 0 = 98 ∧ heapOf 0 1 0 = 90 ∧ heapOf 0 0 1 = 448 ∧
  tLeaf < 98 ∧ tExt < 90 ∧ tBranch < 448

/-- Exact singleton costs and strict per-byte rate below one. -/
theorem node_ticks_non_vacuous_and_tight : ExactTicks := by unfold ExactTicks; decide

/-- Heap domination, with singleton witnesses retaining exact tick values. -/
theorem ticks_le_heap_non_vacuous_and_tight :
    (∀ L E B, decodeTicks L E B ≤ heapOf L E B) ∧
    (∀ L E B, heapOf L E B ≤ heapAvail → decodeTicks L E B ≤ 31092374808) ∧
    decodeTicks 1 0 0 = 43 ∧ decodeTicks 0 1 0 = 48 ∧ decodeTicks 0 0 1 = 326 :=
  ⟨ticks_le_heap, decode_linear, rfl, rfl, rfl⟩

/-- The DAG maximum is attained by the all-branch population. -/
theorem decode_memo_non_vacuous_and_tight :
    (∀ L E B n, 4 * n ≤ 134217712 → L + E + B ≤ n →
      decodeTicks L E B ≤ 10938743528) ∧
    decodeTicks 0 0 33554428 = 10938743528 ∧
    4 * 33554428 = 134217712 ∧
    yukon - 10938743528 = 889781181946 ∧ 10938743528 < yukon := by
  refine ⟨?_, by decide, by decide, decode_memo_val.2, by decide⟩
  intro L E B n hn h
  exact (decode_memo L E B n hn h).1

/-- Heap-bounded decode fits Yukon even at five times the tick count. -/
theorem heap_yukon_non_vacuous_and_tight :
    (∀ L E B, heapOf L E B ≤ heapAvail → 5 * decodeTicks L E B < yukon) ∧
    heapAvail = 31092374808 ∧
    28 * heapAvail < yukon ∧ yukon < 29 * heapAvail :=
  ⟨decode_under_5x, rfl, by decide, by decide⟩

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.StackToLabAndLabToTargetNoLocValue6
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


/-- Joint MPT, nodedb and ts+64 envelope with exact fivefold margin. -/
theorem joint_bridge_non_vacuous_and_tight :
    GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
    5 * GuestMptNodedbAndTransientStorageBridge.joint = 880629318265 ∧
    yukon - 5 * GuestMptNodedbAndTransientStorageBridge.joint = 20090607209 ∧
    5 * GuestMptNodedbAndTransientStorageBridge.joint < yukon :=
  StackToLabNoLocValue6AndFiftySixBudgetBridge.mpt_nodedb_five_times_non_vacuous_and_tight

/-- Preserve the bounded-build and transient-storage absorption hypotheses. -/
theorem absorption_non_vacuous_and_tight :
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.AbsorptionContract :=
  GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster.bridge_absorption_non_vacuous_and_tight

def SixtyShape : Prop :=
  portfolio.length = 60 ∧ portfolio.Pairwise (· < ·) ∧
  (∀ K ∈ portfolio, 1212035192 ≤ K ∧ K < yukon) ∧
  portfolio.take 58 = Previous ∧
  portfolio.drop 58 = [880629318269, 880629318270] ∧
  portfolio.getLast? = some 880629318270 ∧ yukon = 900719925474

def ClaimPayloads : Prop :=
  sixtyClaims.length = 60 ∧ sixtyClaims.map Prod.fst = portfolio ∧
  (∀ e ∈ sixtyClaims, e.2.utf8ByteSize ≤ 128 ∧ validFiniteClaim e.1 e.2 = true) ∧
  sixtyClaims.take 58 = GuestMptNodedbFiftyFourBridgeAndFiftyEightBudgetMaster.fiftyEightClaims

/-- Exact increasing sixty-element portfolio, preserving the full prefix. -/
theorem portfolio_non_vacuous_and_tight : SixtyShape := by
  unfold SixtyShape
  decide

/-- Exact valid JSON payloads, also preserving the full prefix. -/
theorem payloads_non_vacuous_and_tight : ClaimPayloads := by
  unfold ClaimPayloads
  decide

/-- All sixty certificates require the explicit base certificate. -/
theorem certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    SixtyShape ∧ (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) := by
  refine ⟨portfolio_non_vacuous_and_tight, ?_⟩
  intro K hK
  exact UnrolledTwelveCandidatePortfolio.certificate_lift_non_vacuous_and_tight
    _ K (portfolio_non_vacuous_and_tight.2.2.1 K hK).1 cert

theorem integrated_master_non_vacuous_and_tight
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
    ExactTicks ∧
    (∀ L E B, heapOf L E B ≤ heapAvail → decodeTicks L E B ≤ 31092374808) ∧
    (decodeTicks 0 0 33554428 = 10938743528 ∧
      yukon - 10938743528 = 889781181946) ∧
    (GuestMptNodedbAndTransientStorageBridge.joint = 176125863653 ∧
      5 * GuestMptNodedbAndTransientStorageBridge.joint < yukon) ∧
    WitnessDagMemoizationMptBridgeAndFiftySixBudgetMaster.AbsorptionContract ∧
    SixtyShape ∧ ClaimPayloads ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨fun s' hs hu => panToTarget_user_sections_noStubJumpOrLocValue arch prog wc ac perf sc dc mh sp
      off ic pos labs ffis L' labs' h s' hs hu,
   node_ticks_non_vacuous_and_tight, decode_linear,
   ⟨decode_memo_non_vacuous_and_tight.2.1, decode_memo_val.2⟩,
   ⟨joint_bridge_non_vacuous_and_tight.1, joint_bridge_non_vacuous_and_tight.2.2.2⟩,
   absorption_non_vacuous_and_tight,
   portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight,
   (certificates_non_vacuous_and_tight cert).2⟩

#print axioms node_ticks_non_vacuous_and_tight
#print axioms ticks_le_heap_non_vacuous_and_tight
#print axioms decode_memo_non_vacuous_and_tight
#print axioms heap_yukon_non_vacuous_and_tight
#print axioms panToTarget_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
#print axioms panToTarget_user_sections_noStubJumpOrLocValue_bridge_non_vacuous_and_tight
#print axioms joint_bridge_non_vacuous_and_tight
#print axioms absorption_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms payloads_non_vacuous_and_tight
#print axioms certificates_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.WitnessDecodeExactTicksNoLocValue6AndSixtyBudgetMaster
