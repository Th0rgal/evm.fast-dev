import Lean.Elab.Tactic.Omega

set_option autoImplicit false

/-!
Transport bounds (AGENTS.md) are distinct from check_submission.py's source
policy: 65536 entries, 16 MiB per file, 4 GiB total, 128 claim bytes.
The results below certify numerical budgets, not a filesystem measurement or
an InitE certificate. In particular the current Solution imports Proofs, and
claim.json is infinity. Deleting Proofs cannot produce a closed package.
No assertion about an actual import closure is inferred from a file count.
-/
namespace InitECandidate.Solver.PurifiedSubmissionBound

/-- Yukon archive transport limits, including the expanded-byte limit. -/
def Transport (archiveBytes extractedEntries expandedBytes : Nat) : Prop :=
  archiveBytes ≤ 25 * 1024 * 1024 ∧ extractedEntries ≤ 10000 ∧
    expandedBytes ≤ 512 * 1024 * 1024

/-- Source-tree limits actually enforced by verifier/check_submission.py. -/
def SourcePolicy (entries largestFile totalBytes claimJsonBytes : Nat) : Prop :=
  entries ≤ 65536 ∧ largestFile ≤ 16 * 1024 * 1024 ∧
    totalBytes ≤ 4 * 1024 * 1024 * 1024 ∧ claimJsonBytes ≤ 128

/-- Finite-score numerical bound; infinity is a separate sentinel. -/
def FiniteScore (K minutes : Nat) : Prop :=
  minutes ≤ 9999 ∧ K * 10^4 + minutes < 2^53 - 1

/-- The archive-byte cap is inclusive and sharp. -/
theorem archive_non_vacuous_and_tight (n : Nat) :
    n ≤ 25 * 1024 * 1024 ↔ n < 26214401 := by omega

/-- The entry cap counts directories too; it is inclusive and sharp. -/
theorem entries_non_vacuous_and_tight (n : Nat) :
    n ≤ 10000 ↔ n < 10001 := by omega

/-- The claim cap is on raw bytes, including whitespace. -/
theorem claim_non_vacuous_and_tight (n : Nat) :
    n ≤ 128 ↔ n < 129 := by omega

/-- Exact expanded-byte transport boundary. -/
theorem expanded_non_vacuous_and_tight (n : Nat) :
    n ≤ 512 * 1024 * 1024 ↔ n < 536870913 := by omega

/-- Exact verifier source-entry boundary, distinct from transport. -/
theorem source_entries_non_vacuous_and_tight (n : Nat) :
    n ≤ 65536 ↔ n < 65537 := by omega

/-- Exact per-file verifier boundary. -/
theorem source_file_non_vacuous_and_tight (n : Nat) :
    n ≤ 16 * 1024 * 1024 ↔ n < 16777217 := by omega

/-- Exact total-source verifier boundary. -/
theorem source_total_non_vacuous_and_tight (n : Nat) :
    n ≤ 4 * 1024 * 1024 * 1024 ↔ n < 4294967297 := by omega

/-- Largest K for which every legal minute suffix is strictly below infinity. -/
theorem uniform_score_non_vacuous_and_tight (K : Nat) :
    (∀ minutes : Nat, minutes ≤ 9999 → FiniteScore K minutes) ↔
      K ≤ 900719925473 := by
  constructor
  · intro h
    have hm := (h 9999 (by omega)).2
    omega
  · intro h minutes hm
    constructor
    · exact hm
    · dsimp [FiniteScore]
      omega

/-- The next K is admissible exactly through suffix 990, not 991. -/
theorem boundary_score_non_vacuous_and_tight (minutes : Nat) :
    FiniteScore 900719925474 minutes ↔ minutes ≤ 990 := by
  unfold FiniteScore
  omega

/-- Conditional material certificate. Archive bytes must be measured separately:
gzip/tar overhead is not bounded solely by source payload bytes. Entries must
include directories, not merely the number of regular files. -/
theorem small_package_material_bounds
    (archiveBytes entries expandedBytes largestFile claimJsonBytes : Nat)
    (ha : archiveBytes < 2 * 1024 * 1024) (he : entries < 35)
    (hx : expandedBytes < 2 * 1024 * 1024)
    (hf : largestFile ≤ expandedBytes) (hc : claimJsonBytes ≤ 128) :
    Transport archiveBytes entries expandedBytes ∧
      SourcePolicy entries largestFile expandedBytes claimJsonBytes := by
  unfold Transport SourcePolicy
  omega

/-- Pure graph arithmetic only: actual closure sizes require a dependency
measurement and a closed replacement certificate, neither follows from tar. -/
theorem measured_graph_reduction (before after : Nat)
    (hb : 53000 < before) (ha : after < 1500) :
    51501 < before - after := by omega

/-- A 56848-entry tree cannot be transported under the 10000-entry cap. -/
theorem full_tree_transport_rejected (a x : Nat) :
    ¬ Transport a 56848 x := by
  unfold Transport
  omega

end InitECandidate.Solver.PurifiedSubmissionBound
