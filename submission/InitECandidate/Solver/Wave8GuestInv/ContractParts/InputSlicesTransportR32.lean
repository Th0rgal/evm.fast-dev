import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.GbodyRunAttempt
import InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesWitnessR32

/-!
# Carrying `WitnessSliceOK` of the input lists along the `run_attempt` spine (R32)

`DecodeStatelessSlicesR32` proves that `decode_host_input` returns an input
struct whose node / code / header slices are all `WitnessSliceOK`.  The
`run_attempt` proof (`GbodyRunAttempt.lean`) keeps, across every call between
`decode_host_input` and `nodedb_build`, the cells of `runAttemptCells`
unhit (`IvlUnhit`) and `heap_ptr` monotone.  This file shows that this is
enough to keep the slice facts: `WitnessSliceOK` only reads the two words of
the slice cell and compares them with `heap_ptr`.

Nothing here is wired into `run_attempt`; these are the transport lemmas a
strengthened `InputAtStrong` would use.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedVariables false

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.GuestTrapAndLookup
open InitECandidate.Solver.HeapPotential
open InitECandidate.Solver.UniformSourceClock
open InitECandidate.Solver.PanTerminatingBounded
open InitECandidate.Solver.PanRunBounded
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards
open InitECandidate.Solver.Wave8GuestInv.Fast_C08WkShard03
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

/-- `WitnessSliceOK` of every cell of a slice array survives a step that leaves
the array unhit and does not lower `heap_ptr`. -/
theorem witnessSlices_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F}
    {arr cnt : Nat}
    (hu : R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post (arr, 16 * cnt))
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (hwok : WordsOK post (arr, 16 * cnt))
    (hhi : arr + 16 * cnt ≤ 2 ^ 64)
    (h : ∀ j, j < cnt → WitnessSliceOK s (arr + 16 * j)) :
    ∀ j, j < cnt → WitnessSliceOK post (arr + 16 * j) := by
  intro j hj
  obtain ⟨_, ⟨hi1, hi2⟩, hl, ⟨hp1, hp2⟩⟩ := h j hj
  have harr_al : arr % 8 = 0 := hwok.1
  have e0 : memW post (arr + 16 * j) = memW s (arr + 16 * j) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hu (by omega) hhi
      ⟨by show arr ≤ arr + 16 * j; omega, by show arr + 16 * j + 8 ≤ arr + 16 * cnt; omega⟩
  have e8 : memW post (arr + 16 * j + 8) = memW s (arr + 16 * j + 8) :=
    R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit hu (by omega) hhi
      ⟨by show arr ≤ arr + 16 * j + 8; omega, by show arr + 16 * j + 8 + 8 ≤ arr + 16 * cnt; omega⟩
  change sourceBase ≤ arr + 16 * j at hi1
  change arr + 16 * j + 16 ≤ globN s "heap_ptr" at hi2
  change sourceBase ≤ memW s (arr + 16 * j) at hp1
  change memW s (arr + 16 * j) + memW s (arr + 16 * j + 8) ≤ globN s "heap_ptr" at hp2
  refine ⟨⟨?_, (by show 16 % 8 = 0; decide), fun k hk => ?_⟩, ⟨?_, ?_⟩, by rw [e8]; exact hl, ⟨?_, ?_⟩⟩
  · show (arr + 16 * j) % 8 = 0
    omega
  · have hk' : k < 16 / 8 := hk
    have h := hwok.2.2 (2 * j + k) (by show 2 * j + k < 16 * cnt / 8; omega)
    have e : arr + 8 * (2 * j + k) = arr + 16 * j + 8 * k := by omega
    rw [← e]; exact h
  · show sourceBase ≤ arr + 16 * j
    omega
  · show arr + 16 * j + 16 ≤ globN post "heap_ptr"
    omega
  · show sourceBase ≤ memW post (arr + 16 * j)
    omega
  · show memW post (arr + 16 * j) + memW post (arr + 16 * j + 8) ≤ globN post "heap_ptr"
    omega

/-- Every slice of the node (`si + 40`), code (`si + 56`) and header
(`si + 72`) lists of the input struct is `WitnessSliceOK`. -/
def InputSlicesOK {F : Type} (s : PanSemStateFiniteExact 64 F) (si : Nat) : Prop :=
  (∀ j, j < memW s (si + 48) → WitnessSliceOK s (memW s (si + 40) + 16 * j)) ∧
  (∀ j, j < memW s (si + 64) → WitnessSliceOK s (memW s (si + 56) + 16 * j)) ∧
  (∀ j, j < memW s (si + 80) → WitnessSliceOK s (memW s (si + 72) + 16 * j))

/-- `InputSlicesOK` is kept by any step that leaves the `runAttemptCells`
unhit and does not lower `heap_ptr` — the shape of every preservation lemma of
`GbodyRunAttempt.lean` (`WorldStep.preserves_inputAtStrongWith` and friends). -/
theorem inputSlicesOK_of_unhit {F : Type} {s post : PanSemStateFiniteExact 64 F} {si : Nat}
    (hc : ∀ i ∈ runAttemptCells s si,
      i.1 % 8 = 0 ∧ Inside i sourceBase (globN s "heap_ptr") ∧ WordsOK s i)
    (hcp : ∀ i ∈ runAttemptCells post si,
      i.1 % 8 = 0 ∧ Inside i sourceBase (globN post "heap_ptr") ∧ WordsOK post i)
    (hlim : globN s "heap_ptr" ≤ heapLimit)
    (hu : ∀ c ∈ runAttemptCells s si, R10Shards.Fast_GbodyC17ToC21.IvlUnhit s post c)
    (hhp : globN s "heap_ptr" ≤ globN post "heap_ptr")
    (h : InputSlicesOK s si) : InputSlicesOK post si := by
  have h264 : heapLimit ≤ 2 ^ 64 := by decide
  have hs := hc (si, 96) (by simp [runAttemptCells])
  have hsi : ∀ off, off % 8 = 0 → off + 8 ≤ 96 →
      memW post (si + off) = memW s (si + off) := by
    intro off ho hb
    exact R10Shards.Fast_GbodyC17ToC21.memW_eq_of_ivlUnhit
      (hu (si, 96) (by simp [runAttemptCells]))
      (by have := hs.1; omega) (by have := hs.2.1.2; omega) ⟨by omega, by omega⟩
  have e40 := hsi 40 (by decide) (by decide)
  have e48 := hsi 48 (by decide) (by decide)
  have e56 := hsi 56 (by decide) (by decide)
  have e64 := hsi 64 (by decide) (by decide)
  have e72 := hsi 72 (by decide) (by decide)
  have e80 := hsi 80 (by decide) (by decide)
  have hgen : ∀ (arr cnt : Nat), (arr, 16 * cnt) ∈ runAttemptCells s si →
      WordsOK post (arr, 16 * cnt) →
      (∀ j, j < cnt → WitnessSliceOK s (arr + 16 * j)) →
      ∀ j, j < cnt → WitnessSliceOK post (arr + 16 * j) := by
    intro arr cnt hmem hwok hsl
    have hin := (hc _ hmem).2.1.2
    change arr + 16 * cnt ≤ globN s "heap_ptr" at hin
    exact witnessSlices_of_unhit (hu _ hmem) hhp hwok (by omega) hsl
  refine ⟨?_, ?_, ?_⟩
  · have hw := (hcp (memW post (si + 40), 16 * memW post (si + 48)) (by simp [runAttemptCells])).2.2
    rw [e40, e48] at hw ⊢
    exact hgen _ _ (by simp [runAttemptCells]) hw h.1
  · have hw := (hcp (memW post (si + 56), 16 * memW post (si + 64)) (by simp [runAttemptCells])).2.2
    rw [e56, e64] at hw ⊢
    exact hgen _ _ (by simp [runAttemptCells]) hw h.2.1
  · have hw := (hcp (memW post (si + 72), 16 * memW post (si + 80)) (by simp [runAttemptCells])).2.2
    rw [e72, e80] at hw ⊢
    exact hgen _ _ (by simp [runAttemptCells]) hw h.2.2

/-- The slice clause of `NodeDbSlicesReady` for the witness-node list, at a
`nodedb_build(si.nodes, si.n_nodes)` call entry. -/
theorem nodeDbSlices_of_inputSlicesOK {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputSlicesOK s si)
    (harr : locN s "slice_arr" = memW s (si + 40)) (hn : locN s "n" = memW s (si + 48)) :
    ∀ j < locN s "n", WitnessSliceOK s (locN s "slice_arr" + 16 * j) := by
  intro j hj
  rw [harr]
  rw [hn] at hj
  exact h.1 j hj

/-- Same for the code list (`nodedb_build(si.codes, si.n_codes)`). -/
theorem codeDbSlices_of_inputSlicesOK {F : Type} {s : PanSemStateFiniteExact 64 F} {si : Nat}
    (h : InputSlicesOK s si)
    (harr : locN s "slice_arr" = memW s (si + 56)) (hn : locN s "n" = memW s (si + 64)) :
    ∀ j < locN s "n", WitnessSliceOK s (locN s "slice_arr" + 16 * j) := by
  intro j hj
  rw [harr]
  rw [hn] at hj
  exact h.2.1 j hj

end InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32
