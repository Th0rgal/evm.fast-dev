import InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall
import InitECandidate.Solver.GuestNodedbAndWitnessTableBound
import InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# `InitECandidate.Solver.SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth`

Self-contained Wave 5 synthesis (`W5_147`) combining:
1. The unconditional `PanSimp` → `WordToWord` → `WordToStack` → `StackToLab` → `LabToTarget`
   section-6 (`storeConstsStubLocation`) unreachability chain (`panToLab_lines`,
   `panToTarget_noStubJump`, `panToTarget_user_sections_noStubJump`).
2. The `guest.pp.pnk` `nodedb` and witness-table capacity, run-length threshold, and
   shared state/code build bounds (`entries_le` ≤ `33,554,428`, `entries_tight`,
   `cap_extreme` = `2^26`, `load_half`, `bounded_build_val` = `536,870,848` ticks for `r = 8`,
   `run_threshold` `r ≤ 13,421`, `two_builds`).
3. The `ts+64` transient storage subcall revert, journal (`restoreDels` ≤ `524,288`),
   run-cap absorption (`≤ 100,000,000,000`), shared 200M-gas coupled slope bound
   (`≤ 746,044,000,000` ticks), and the strictly increasing 52-budget portfolio under
   the Yukon ceiling (`900,719,925,474`) with explicit finite certificates lifted from
   the base certificate hypothesis.
-/

namespace InitECandidate.Solver.SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth

open Flapjack
open Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang
open Flapjack.Compiler.Backend.LabToTarget
open Flapjack.Compiler.Backend.LabFilter
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Encoders.Asm
open InitECandidate.Solver.WordPassesPreserveNoStoreConsts
open InitECandidate.Solver.PanToStackNoStoreConsts
open InitECandidate.Solver.StackRemoveAndNamesNoStoreConsts
open InitECandidate.Solver.WordToWordNoStubCall
open InitECandidate.Solver.PanToLabSectionAndStackRemoveClock
open InitECandidate.Solver.StackToLabAndLabToTargetNoStubCall
open InitECandidate.Solver.GuestNodedbAndWitnessTableBound
open InitECandidate.Solver.TransientStorageSubcallRevertJournalAndFiftyTwoBudgetMaster
open _root_.InitECandidate.Solver.GuestTransientStorageAndRemainingTablesAudit (buildTicks)
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

variable {width : Nat} [NeZero width]

/-- 1. Stack-level and `StackToLab.flattenHOL` invariants (`JC`, `clean_eq`, `c_body_chain`,
`sec_ok`) paired with tightness witnesses showing that direct calls/jumps to section 6
(`storeConstsStubLocation`) are rejected while user calls are accepted. -/
theorem stack_and_flatten_invariants_non_vacuous_and_tight
    (f : Spt Nat) (sid next : Nat) (cs bs : List Nat) :
    (∀ p : HolProg width, JC p = (StackNoSt p && J p)) ∧
    (∀ (info : Spt Nat) (j : Bool) (bd : BitVec width × BitVec width) (ptr n : Nat) (p : HolProg width),
      JC p = true →
      JC (StackNames.progCompHOL f (StackRemove.comp j bd ptr
        (StackAlloc.progComp (n, StackRawCall.compTop info p)).2)) = true) ∧
    (∀ (n : Nat) (p : HolProg width), n ≠ storeConstsStubLocation → JC p = true →
      LOk (StackToLab.progToSectionHOL (n, p)).lines) ∧
    StackNoSt (StackNames.progCompHOL f (.storeConsts 0 1 none : HolProg width)) = false ∧
    JC (.rawCall storeConstsStubLocation : HolProg width) = false ∧
    ¬ AOk (StackToLab.flattenHOL false (.rawCall storeConstsStubLocation : HolProg width) sid next cs bs).1 ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true :=
  ⟨clean_eq,
   fun info j bd ptr n p hp => c_body_chain info j bd ptr f n p hp,
   sec_ok,
   StackToLabAndLabToTargetNoStubCall.stackNames_keeps_storeConsts f,
   jc_rejects_rawCall_stub,
   flatten_rawCall_stub_tight sid next cs bs,
   jumpOk_rejects_stub,
   jumpOk_accepts_user⟩

/-- 2. Unconditional `PanSimp` → … → `StackToLab` section-line guarantee (`panToLab_lines`):
every produced section is either a stub section or satisfies `LOk s.lines` (no jump or call
into section `storeConstsStubLocation`), with no hypothesis on the Pancake program. -/
theorem panToLab_lines_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    (∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ LOk s.lines) ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true :=
  ⟨panToLab_lines arch prog wc ac perf sc dc mh sp off,
   jumpOk_rejects_stub,
   jumpOk_accepts_user⟩

/-- 3. Full `PanSimp` → … → `LabToTarget` (`filterSkip` + `removeLabels`) preservation
(`panToTarget_noStubJump`): every encoded section is either a stub section or has `JumpOk x = true`
for all its lines, without any hypothesis on the Pancake program. -/
theorem panToTarget_noStubJump_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true :=
  ⟨fun ic pos labs ffis L' labs' h =>
     panToTarget_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
   jumpOk_rejects_stub,
   jumpOk_accepts_user⟩

/-- 4. User-section corollary after `LabToTarget` (`panToTarget_user_noStubJump`):
after `filterSkip` and `removeLabels`, no user section (`IsStubLabel s'.sectionId = false`)
contains a jump, conditional jump, or call targeting section 6 (`storeConstsStubLocation`),
with no hypothesis on the Pancake program. -/
theorem panToTarget_user_noStubJump_non_vacuous_and_tight (arch : AsmArchitecture)
    (prog : List (Pancake.PanLang.DeclHOL width)) (wc : WordToWord.Config)
    (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width) :
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      ∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true) ∧
    IsStubLabel (storeConstsStubLocation : Nat) = true ∧
    IsStubLabel (64 : Nat) = false ∧
    JumpOk (.labAsm (.jump (.lab storeConstsStubLocation 0)) (0 : BitVec width) [] 0) = false ∧
    JumpOk (.labAsm (.call (.lab 64 0)) (0 : BitVec width) [] 0) = true :=
  ⟨fun ic pos labs ffis L' labs' h s' hs hu =>
     panToTarget_user_sections_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu,
   by decide,
   by decide,
   jumpOk_rejects_stub,
   jumpOk_accepts_user⟩

/-- 5. `nodedb` SSZ entry bound (`entries_le` ≤ `33,554,428`, `entries_tight`), power-of-two
capacity at the extreme (`cap_extreme` = `2^26 = 67,108,864`), and `≤ 1/2` load factor
(`load_half`, no `htab_grow`). -/
theorem nodedb_entries_and_capacity_non_vacuous_and_tight :
    (∀ n : Nat, 4 * n ≤ maxInput → n ≤ 33554428) ∧
    4 * 33554428 = maxInput ∧
    (2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2) ∧
    (∀ n c : Nat, 2 * n + 2 ≤ c → (n + 1) * 2 ≤ c) ∧
    (capOf 0 = 4 ∧ capOf 1 = 4 ∧ capOf 2 = 8 ∧ capOf 7 = 16) :=
  ⟨entries_le, entries_tight, cap_extreme, load_half, cap_small⟩

/-- 6. `nodedb` build probe analysis: adversarial single-run worst case (`worst_build_val`),
linear bounded-run build (`bounded_build_val` = `536,870,848` ticks at `r = 8`), exact Yukon
run-length threshold (`run_threshold`: `r ≤ 13,421`), monotonicity, Keccak grinding cost,
and shared state+code input budget (`two_builds`). -/
theorem nodedb_build_and_two_builds_non_vacuous_and_tight :
    (worstBuild 33554428 = 1125899604852756 ∧ yukon < worstBuild 33554428) ∧
    (boundedBuild 8 33554428 = 536870848 ∧ boundedBuild 8 33554428 < yukon) ∧
    (boundedBuild 13421 33554428 < yukon ∧ yukon < boundedBuild 13422 33554428) ∧
    (∀ r a b : Nat, a ≤ b → boundedBuild r a ≤ boundedBuild r b) ∧
    33554428 * 67108864 / 2 = 1125899772624896 ∧
    (∀ r ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
      boundedBuild r ns + boundedBuild r nc ≤ boundedBuild r 33554428) :=
  ⟨worst_build_val, bounded_build_val, run_threshold, bounded_mono, grind_cost, two_builds⟩

/-- 7. `ts+64` subcall splitting (`split_le`), rollback/halving witnesses, sharp run-cap
thresholds (`L ≤ 5,000` with revert, `L ≤ 10,000` without revert), and universal run-cap
absorption (`absorbed_with_cap` ≤ `100,000,000,000` ticks). -/
theorem transient_split_revert_and_cap_absorption_non_vacuous_and_tight (l : List Nat) (L : Nat) :
    ((l.map buildTicks).sum ≤ buildTicks l.sum ∧
      buildTicks 2 + buildTicks 2 = 10 ∧ buildTicks 4 = 30 ∧
      buildTicks 2 + buildTicks 2 < buildTicks 4 ∧
      ([158162].map buildTicks).sum = buildTicks ([158162].sum)) ∧
    (2 * buildTicks 158162 = 125075300410 ∧
      2 * buildTicks 79081 = 31268627400 ∧ buildTicks 158162 = 62537650205) ∧
    ((10 * L ≤ 50000 ↔ L ≤ 5000) ∧ (5 * L ≤ 50000 ↔ L ≤ 10000) ∧
      (10 * 5000 = 50000 ∧ 50000 < 10 * 5001 ∧
       5 * 10000 = 50000 ∧ 50000 < 5 * 10001)) ∧
    ((∀ L' n u B blk : Nat, L' ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
        40 * blk ≤ B * B → blk + 10 * L' * n ≤ 100000000000) ∧
      (10 * 5000 * 2000000 = 100000000000) ∧
      100000000000 ≤ 156088992805 ∧
      5 * 156088992805 < yukon ∧ yukon < 6 * 156088992805 ∧ 5000 < 158162) :=
  ⟨split_non_vacuous_and_tight l,
   revert_and_half_non_vacuous_and_tight,
   thresholds_non_vacuous_and_tight L,
   cap_absorption_non_vacuous_and_tight⟩

/-- 8. Shared 200M-gas convex coupling (`coupled_le` ≤ `746,044,000,000` ticks), Yukon headroom
(`150,516,361,240` ticks), journal restoration bound (`restoreDels` ≤ `524,288`), exact
per-gas slope (`373,022`), and the preceding remaining-table contracts. -/
theorem transient_coupled_yukon_journal_and_slope_non_vacuous_and_tight :
    ((∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
        t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
      100 * 2000000 = 200000000 ∧
      373022 * 2000000 + 373022 * 0 = 746044000000 ∧
      11 * buildTicks 158162 + buildTicks 145647 = 740946409660 ∧
      746044000000 - 740946409660 = 5097590340) ∧
    ((746044000000 + 4159564234 < yukon ∧
        yukon - (746044000000 + 4159564234) = 150516361240 ∧
        yukon < 2 * (740946409660 + 4159564234)) ∧
      746044000000 < 740946409660 + 156088992805) ∧
    ((∀ j : List Bool, j.length ≤ 524288 →
        _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
      _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels
        (List.replicate 524288 false) = 524288 ∧
      (_root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels [false, true, false] = 2 ∧
       _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels [true, true] = 0) ∧
      ((1 + 1 : Nat) = 2 ∧ (1 + 1 + 1 : Nat) = 3)) ∧
    ((∀ k : Nat, k ≤ 158162 → 100 * buildTicks k ≤ 373022 * (106 * k)) ∧
      ¬ (250 * (158162 - 1) ≤ 106 * 373021) ∧
      (2000000 / 20 / 2 + 13 * 167772 / 84 + 1 = 75965 ∧ 75965 < 373022)) ∧
    (_root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.KeyCap ∧
     _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.PackingAndBuild ∧
     _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.BlockCosts ∧
     _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.OneSlopeMargin ∧
     _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.TransientObstruction ∧
     _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables) :=
  ⟨coupled_non_vacuous_and_tight,
   yukon_margin_non_vacuous_and_tight,
   journal_non_vacuous_and_tight,
   slope_non_vacuous_and_tight,
   previous_analysis_non_vacuous_and_tight⟩

/-- 9. Strictly increasing 52-budget portfolio (`FiftyTwoShape`) below the Yukon ceiling
(`900,719,925,474`) and its 52 explicit validated finite JSON claim payloads (`ClaimPayloads`). -/
theorem fifty_two_portfolio_and_payloads_non_vacuous_and_tight :
    FiftyTwoShape ∧ ClaimPayloads :=
  ⟨fifty_two_shape_non_vacuous_and_tight, fifty_two_payloads_non_vacuous_and_tight⟩

/-- 10. Grand self-contained synthesis (`W5_147`): unites the unconditional `PanSimp` → `LabToTarget`
no-stub-jump theorems (`panToLab_lines`, `panToTarget_noStubJump`, `panToTarget_user_sections_noStubJump`),
the `nodedb` entry/capacity/run-threshold/two-builds theorems, the `ts+64` splitting/cap-absorption/
coupled-gas/journal theorems, and the 52-budget portfolio with explicit finite certificates lifted
from the base certificate `cert : CertificateAt 1212035192`. -/
theorem self_contained_lab_to_target_nodedb_and_fifty_two_budget_master_non_vacuous_and_tight
    (arch : AsmArchitecture) (prog : List (Pancake.PanLang.DeclHOL width))
    (wc : WordToWord.Config) (ac : AsmConfigExact width) (perf : Bool)
    (sc : StackToLab.Config) (dc : DataToWord.Config) (mh sp : Nat)
    (off : BitVec width × BitVec width)
    (cert : CertificateAt 1212035192) :
    (∀ s ∈ StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2,
      IsStubLabel s.sectionId = true ∨ LOk s.lines) ∧
    (∀ (ic pos : Nat) (labs : Spt (Spt Nat)) (ffis : List HolFfiName)
        (L' : List (Sec width)) (labs' : Spt (Spt Nat)),
      removeLabels ic ac pos labs ffis (filterSkip (StackToLab.compile sc dc mh sp off
        (compileNative ac perf (WordToWord.compile wc ac
          (panToWordCompileProgHOL arch prog)).2).2.2.2)) = some (L', labs') →
      (∀ s' ∈ L', IsStubLabel s'.sectionId = true ∨ ∀ x ∈ s'.lines, JumpOk x = true) ∧
      (∀ s' ∈ L', IsStubLabel s'.sectionId = false → ∀ x ∈ s'.lines, JumpOk x = true)) ∧
    ((∀ n : Nat, 4 * n ≤ maxInput → n ≤ 33554428) ∧
      4 * 33554428 = maxInput ∧
      (2 * 33554428 + 2 ≤ 67108864 ∧ 33554432 < 2 * 33554428 + 2) ∧
      (∀ n c : Nat, 2 * n + 2 ≤ c → (n + 1) * 2 ≤ c) ∧
      (boundedBuild 8 33554428 = 536870848 ∧ boundedBuild 8 33554428 < yukon) ∧
      (boundedBuild 13421 33554428 < yukon ∧ yukon < boundedBuild 13422 33554428) ∧
      (∀ r ns nc : Nat, 4 * (ns + nc) ≤ maxInput →
        boundedBuild r ns + boundedBuild r nc ≤ boundedBuild r 33554428)) ∧
    (FiftyTwoShape ∧ ClaimPayloads ∧
      (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) ∧
      (∀ l : List Nat, (l.map buildTicks).sum ≤ buildTicks l.sum) ∧
      (∀ j : List Bool, j.length ≤ 524288 →
        _root_.InitECandidate.Solver.GuestTransientStorageGrowthAndJournalAnalysis.restoreDels j ≤ 524288) ∧
      (∀ u1 u2 t1 t2 : Nat, u1 + u2 ≤ 2000000 → t1 ≤ 373022 * u1 →
        t2 ≤ 373022 * u2 → t1 + t2 ≤ 746044000000) ∧
      (∀ L n u B blk : Nat, L ≤ 5000 → n ≤ u → B + u ≤ 2000000 →
        40 * blk ≤ B * B → blk + 10 * L * n ≤ 100000000000) ∧
      _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.KeyCap ∧
      _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.PackingAndBuild ∧
      _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.BlockCosts ∧
      _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.OneSlopeMargin ∧
      _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.TransientObstruction ∧
      _root_.InitECandidate.Solver.TransientStorageRemainingTablesAndFiftyBudgetMaster.RemainingTables) :=
  ⟨panToLab_lines arch prog wc ac perf sc dc mh sp off,
   fun ic pos labs ffis L' labs' h =>
     ⟨panToTarget_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h,
      fun s' hs hu =>
        panToTarget_user_sections_noStubJump arch prog wc ac perf sc dc mh sp off ic pos labs ffis L' labs' h s' hs hu⟩,
   ⟨entries_le, entries_tight, cap_extreme, load_half, bounded_build_val, run_threshold, two_builds⟩,
   integrated_master_non_vacuous_and_tight cert⟩

#print axioms stack_and_flatten_invariants_non_vacuous_and_tight
#print axioms panToLab_lines_non_vacuous_and_tight
#print axioms panToTarget_noStubJump_non_vacuous_and_tight
#print axioms panToTarget_user_noStubJump_non_vacuous_and_tight
#print axioms nodedb_entries_and_capacity_non_vacuous_and_tight
#print axioms nodedb_build_and_two_builds_non_vacuous_and_tight
#print axioms transient_split_revert_and_cap_absorption_non_vacuous_and_tight
#print axioms transient_coupled_yukon_journal_and_slope_non_vacuous_and_tight
#print axioms fifty_two_portfolio_and_payloads_non_vacuous_and_tight
#print axioms self_contained_lab_to_target_nodedb_and_fifty_two_budget_master_non_vacuous_and_tight

end InitECandidate.Solver.SelfContainedLabToTargetNoStubJumpAndFiftyTwoBudgetSynth
