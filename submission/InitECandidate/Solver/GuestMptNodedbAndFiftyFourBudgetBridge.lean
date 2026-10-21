import InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge
import InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster
import InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

/-!
# GuestMptNodedbAndFiftyFourBudgetBridge

Wave 5 bridge (W5_156). No InitECandidate.Proofs.Bounded* import.
-/

namespace InitECandidate.Solver.GuestMptNodedbAndFiftyFourBudgetBridge

open InitECandidate.Solver.GuestMptNodedbAndTransientStorageBridge
open InitECandidate.Solver.MptTraversalStateRootAndFiftyFourBudgetMaster
open InitECandidate.Solver.SelfContainedWitnessDecodeExtensionNibbleAndFiftyTwoBudgetSynth
open _root_.InitECandidate.Solver.GuestJointBlockGasHtabBound (yukon)
open _root_.InitECandidate.Solver.UnrolledTwelveCandidatePortfolio (CertificateAt)
open _root_.InitECandidate.Solver.SelfContainedBoundedCertificate (baselineWithFiniteK)

/-- 1. MPT plus bounded-run nodedb build: 20_036_870_848 ticks, between 44x and 45x under Yukon. -/
theorem mpt_plus_nodedb_budget_non_vacuous_and_tight :
    mptPlusBuild = 20036870848 ∧
    44 * mptPlusBuild < yukon ∧ yukon ≤ 45 * mptPlusBuild :=
  ⟨sum_val, sum_margin.1, sum_margin.2⟩

/-- 2. Combined envelope 176_125_863_653; at 5x it is 880_629_318_265, margin 20_090_607_209. -/
theorem joint_envelope_five_times_non_vacuous_and_tight :
    joint = 176125863653 ∧
    yukon - joint = 724594061821 ∧
    5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209 ∧
    5 * joint < yukon :=
  ⟨joint_val, joint_once, joint_five.1, joint_five.2,
   Nat.lt_of_sub_ne_zero (joint_five.2 ▸ (by decide : 20090607209 ≠ 0))⟩

/-- 3. The joint budget covers the storage envelope, the MPT budget and both builds. -/
theorem joint_covers_two_builds_non_vacuous_and_tight (ns nc : Nat)
    (h : 4 * (ns + nc) ≤
      InitECandidate.Solver.GuestNodedbAndWitnessTableBound.maxInput) :
    156088992805 + 19500000000 +
      InitECandidate.Solver.GuestNodedbAndWitnessTableBound.boundedBuild 8 ns +
      InitECandidate.Solver.GuestNodedbAndWitnessTableBound.boundedBuild 8 nc ≤ joint ∧
    joint = 176125863653 :=
  ⟨joint_covers ns nc h, joint_val⟩

/-- 4. Zero-length extensions are rejected and an accepted extension advances the walk. -/
theorem ext_zero_rejected_and_accepted_advances_non_vacuous_and_tight (ck l : Nat) :
    InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false ∧
    (InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted l 2 = false ∧
     InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted l 1 = false) ∧
    (∀ l' ck' : Nat,
      InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted l' ck' = true →
      1 ≤ InitECandidate.Solver.GuestMptTraversalAndStateRootBound.advance
        (.ext l')) :=
  ⟨(compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight ck l).2.2.2.1,
   (compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight ck l).2.2.2.2.1,
   (compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight ck l).2.2.2.2.2.1⟩

/-- 5. A decoded trie has at most 64 advancing steps, hence at most 65 iterations, and the
bump allocator holds at most 555_220_978 minimum-size nodes. -/
theorem walk_bound_decoded_and_heap_nodes_non_vacuous_and_tight :
    (∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
      ((l.map InitECandidate.Solver.GuestMptTraversalAndStateRootBound.Step.ext).map
        InitECandidate.Solver.GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 →
      l.length ≤ 64 ∧ l.length + 1 ≤ 65) ∧
    (33806089496 - 2713714688) / 56 = 555220978 :=
  ⟨(decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight).1,
   (decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight).2.2.2.1⟩

/-- 6. panToTarget_noStubJump: no section produced by removeLabels jumps to the section-6 stub. -/
theorem panToTarget_noStubJump_bridge_non_vacuous_and_tight : PanTargetSafe :=
  panToTarget_noStubJump_non_vacuous_and_tight

/-- 7. panToTarget_user_noStubJump: no user section reaches the section-6 stub. -/
theorem panToTarget_user_noStubJump_bridge_non_vacuous_and_tight : PanUserSafe :=
  panToTarget_user_noStubJump_non_vacuous_and_tight

/-- 8. The 54-budget portfolio is strictly increasing, every budget is strictly under Yukon
900_719_925_474, and the claim payloads match. -/
theorem fifty_four_portfolio_under_yukon_non_vacuous_and_tight :
    FiftyFourShape ∧ ClaimPayloads ∧ yukon = 900719925474 :=
  ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight, rfl⟩

/-- 9. Every one of the 54 budgets carries a finite certificate, from one base certificate. -/
theorem fifty_four_certificates_non_vacuous_and_tight (cert : CertificateAt 1212035192) :
    FiftyFourShape ∧
    (∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨portfolio_non_vacuous_and_tight, certificates_non_vacuous_and_tight cert⟩

/-- 10. Grand bridge: MPT+nodedb joint envelope, extension rejection, decoded walk bound, heap
capacity, both LabToTarget no-stub-jump theorems, and the 54-budget portfolio under Yukon. -/
theorem guest_mpt_nodedb_and_fifty_four_budget_bridge_master_non_vacuous_and_tight
    (cert : CertificateAt 1212035192) (ck : Nat) :
    (mptPlusBuild = 20036870848 ∧ joint = 176125863653 ∧
      5 * joint = 880629318265 ∧ yukon - 5 * joint = 20090607209) ∧
    InitECandidate.Solver.GuestWitnessDecodeAndExtensionNibbleAudit.extAccepted 0 ck = false ∧
    ((∀ l : List Nat, (∀ x ∈ l, x ≠ 0) →
      ((l.map InitECandidate.Solver.GuestMptTraversalAndStateRootBound.Step.ext).map
        InitECandidate.Solver.GuestMptTraversalAndStateRootBound.advance).sum ≤ 64 →
      l.length + 1 ≤ 65) ∧
     (33806089496 - 2713714688) / 56 = 555220978) ∧
    PanTargetSafe ∧ PanUserSafe ∧
    (FiftyFourShape ∧ ClaimPayloads ∧
      ∀ K ∈ portfolio, InitE.Certificate (baselineWithFiniteK K) (.finite K)) :=
  ⟨⟨sum_val, joint_val, joint_five.1, joint_five.2⟩,
   (compact_to_nibbles_and_extension_rejection_non_vacuous_and_tight ck 0).2.2.2.1,
   ⟨fun l hacc hsum =>
      (decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight).1
        l hacc hsum |>.2,
    (decoded_trie_walk_bound_and_witness_heap_expansion_non_vacuous_and_tight).2.2.2.1⟩,
   panToTarget_noStubJump_non_vacuous_and_tight,
   panToTarget_user_noStubJump_non_vacuous_and_tight,
   ⟨portfolio_non_vacuous_and_tight, payloads_non_vacuous_and_tight,
    certificates_non_vacuous_and_tight cert⟩⟩

end InitECandidate.Solver.GuestMptNodedbAndFiftyFourBudgetBridge
