import InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall
import InitECandidate.Solver.GuestNodedbAndWitnessTableBound
import InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-! W5_146: compiler cleanliness, input-shared nodedb bounds, transient journal
arithmetic and 52 finite claims. Run caps remain explicit model assumptions;
semantic certificates retain the base certificate obligation. -/
namespace InitECandidate.Solver.LabToTargetNoStubJumpNodedbAndFiftyTwoBudgetMaster

open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open InitECandidate.Solver
open StackToLabAndLabToTargetNoStubCall
open GuestNodedbAndWitnessTableBound
open _root_.InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (buildTicks)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

theorem panToLab_lines_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    ∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      PanToLabSectionAndStackRemoveClock.IsStubLabel s.sectionId = true ∨ LOk s.lines :=
  StackToLabAndLabToTargetNoStubCall.panToLab_lines arch prog wc ac perf sc dc mh sp off

theorem panToTarget_noStubJump_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs')) :
    ∀ s' ∈ L', PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = true ∨
      ∀ x ∈ s'.lines, JumpOk x = true :=
  StackToLabAndLabToTargetNoStubCall.panToTarget_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h

theorem panToTarget_user_noStubJump_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
    (L' : List (Sec width)) (labs' : Spt (Spt Nat))
    (h : removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs'))
    (s' : Sec width) (hs : s' ∈ L')
    (hu : PanToLabSectionAndStackRemoveClock.IsStubLabel s'.sectionId = false) :
    ∀ x ∈ s'.lines, JumpOk x = true :=
  StackToLabAndLabToTargetNoStubCall.panToTarget_user_sections_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu

/-- The maximal entry count is attained by the offset-only input. -/
theorem entries_non_vacuous_and_tight :
    (∀ n : Nat, 4 * n ≤ maxInput → n ≤ 33554428) ∧
    4 * 33554428 = maxInput ∧ maxInput < 4 * 33554429 :=
  ⟨entries_le, entries_tight, by decide⟩

/-- Both sides of the power-of-two boundary and the attained half-load bound. -/
theorem capacity_non_vacuous_and_tight :
    (2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2) ∧
    67108864 = 2^26 ∧
    (∀ n c : Nat, 2 * n + 2 ≤ c → (n + 1) * 2 ≤ c) ∧
    (33554428 + 1) * 2 = 67108858 ∧
    (capOf 0 = 4 ∧ capOf 1 = 4 ∧ capOf 2 = 8 ∧ capOf 7 = 16) :=
  ⟨cap_extreme, by decide, load_half, by decide, cap_small⟩

theorem bounded_build_non_vacuous_and_tight :
    (boundedBuild 8 33554428 = 536870848 ∧ boundedBuild 8 33554428 < yukon) ∧
    (worstBuild 33554428 = 1125899604852756 ∧ yukon < worstBuild 33554428) ∧
    (∀ r a b : Nat, a ≤ b → boundedBuild r a ≤ boundedBuild r b) :=
  ⟨bounded_build_val, worst_build_val, bounded_mono⟩

/-- The admissible run threshold is exact, including the first excluded value. -/
theorem run_threshold_non_vacuous_and_tight :
    (∀ r : Nat, boundedBuild r 33554428 < yukon ↔ r ≤ 13421) ∧
    (boundedBuild 13421 33554428 < yukon ∧ yukon < boundedBuild 13422 33554428) := by
  refine ⟨?_, run_threshold⟩
  intro r
  unfold boundedBuild GuestJointBlockGasHtabBound.yukon
  omega

/-- Shared input; equality is attained with both state and code nonempty. -/
theorem two_builds_non_vacuous_and_tight :
    (∀ r ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      boundedBuild r ns + boundedBuild r nc ≤ boundedBuild r 33554428) ∧
    4 * (16777214 + 16777214) = maxInput ∧
    boundedBuild 8 16777214 + boundedBuild 8 16777214 = 536870848 :=
  ⟨two_builds, by decide, by decide⟩

/-- Quadratic splitting, explicit run-cap absorption and shared-gas coupling. -/
theorem transient_non_vacuous_and_tight :
    (∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
    (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
      40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
    (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
      t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
    buildTicks 2 + buildTicks 2 < buildTicks 4 ∧
    10 * 5000 * 2000000 = 100000000000 ∧
    373022 * 2000000 + 373022 * 0 = 746044000000 :=
  ⟨GuestTransientStorageSubcallRevertAndAbsorption.split_le,
   GuestTransientStorageSubcallRevertAndAbsorption.absorbed_with_cap,
   GuestTransientStorageGrowthAndJournalAnalysis.coupled_le,
   by decide, by decide, by decide⟩

theorem journal_non_vacuous_and_tight :
    (∀ j : List Bool, j.length ≤ 524288 →
      GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
    GuestTransientStorageGrowthAndJournalAnalysis.restoreDels
      (List.replicate 524288 false) = 524288 ∧
    (2 * buildTicks 158162 = 125075300410 ∧
     2 * buildTicks 79081 = 31268627400 ∧ buildTicks 158162 = 62537650205) :=
  ⟨GuestTransientStorageGrowthAndJournalAnalysis.restore_once,
   List.count_replicate_self,
   TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.revert_and_half_non_vacuous_and_tight⟩

theorem portfolio_non_vacuous_and_tight :
    TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.FiftyTwoShape ∧
    TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.ClaimPayloads :=
  ⟨TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.fifty_two_shape_non_vacuous_and_tight,
   TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.fifty_two_payloads_non_vacuous_and_tight⟩

/-- Full unconditional source-to-Lab cleanliness, conditional successful encoding,
input-shared nodedb cost, journal/gas contracts and semantic lifting of all tiers.
No restriction on the Pancake program is used. -/
theorem integrated_master_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) (cert : CertificateAt 1212035192) :
    (∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      PanToLabSectionAndStackRemoveClock.IsStubLabel s.sectionId = true ∨ LOk s.lines) ∧
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
      (out : List (Sec width)) (labsOut : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (out, labsOut) →
      ∀ s ∈ out, PanToLabSectionAndStackRemoveClock.IsStubLabel s.sectionId = false →
        ∀ x ∈ s.lines, JumpOk x = true) ∧
    (∀ r ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      boundedBuild r ns + boundedBuild r nc ≤ boundedBuild r 33554428) ∧
    TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.FiftyTwoShape ∧
    TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.ClaimPayloads ∧
    (∀ K ∈ TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.portfolio,
      InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
    (∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
    (∀ j : List Bool, j.length ≤ 524288 →
      GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
    (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
      t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
    (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
      40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) := by
  have master := TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster.integrated_master_non_vacuous_and_tight cert
  exact ⟨panToLab_lines arch prog wc ac perf sc dc mh sp off,
    fun ic pos labs ffis out labsOut h s hs hu =>
      panToTarget_user_sections_noStubJump arch prog wc ac perf sc dc mh sp off
        ic pos labs ffis out labsOut h s hs hu,
    two_builds, master.1, master.2.1, master.2.2.1,
    master.2.2.2.1, master.2.2.2.2.1, master.2.2.2.2.2.1,
    master.2.2.2.2.2.2.1⟩

#print axioms panToLab_lines_non_vacuous_and_tight
#print axioms panToTarget_noStubJump_non_vacuous_and_tight
#print axioms panToTarget_user_noStubJump_non_vacuous_and_tight
#print axioms entries_non_vacuous_and_tight
#print axioms capacity_non_vacuous_and_tight
#print axioms bounded_build_non_vacuous_and_tight
#print axioms run_threshold_non_vacuous_and_tight
#print axioms two_builds_non_vacuous_and_tight
#print axioms transient_non_vacuous_and_tight
#print axioms journal_non_vacuous_and_tight
#print axioms portfolio_non_vacuous_and_tight
#print axioms integrated_master_non_vacuous_and_tight

end InitECandidate.Solver.LabToTargetNoStubJumpNodedbAndFiftyTwoBudgetMaster
