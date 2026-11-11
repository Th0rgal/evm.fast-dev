import InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk.WkHostPayloadHeaders
import InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32

/-! Wave 8 R32 Slot 8 (RunAttemptHtrR32), obligation A.

`htr_new_payload_request` keeps the world under the R32-weakened input guard
`HtrNewPayloadReadyR32`: `HtrNewPayloadReady` with `InputAt` replaced by `InputAtR32`,
whose per-cell `Inside` requirement is weakened to "null pair `(0, 0)` or `Inside`" —
the shape decode produces for empty lists. The strong `Inside` facts for the four
`inputCells` cells are recovered from the seven `runAttemptCells` cells of
`InputAtR32With` (six of the seven cells coincide; the `(si, 40)` header cell is a
sub-interval of the `(si, 96)` run-attempt header cell), and the strong theorem is
applied through `«wk_htr_new_payload_request_guarded»`. -/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8GuestInv.ContractParts.WkHtrNewPayloadR32

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE
open InitECandidate.Solver.Wave8GuestInv
open InitECandidate.Solver.Wave8GuestInv.R16Shards.TopGbodyWk
open InitECandidate.Solver.Wave8GuestInv.ContractParts.GbodyRunAttemptR32

/-- `HtrNewPayloadReady` with `InputAt` weakened to `InputAtR32`. -/
def HtrNewPayloadReadyR32 : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop :=
  fun s =>
    InputAtR32 s (locN s "si") ∧
    IvlsDisj (inputCells s (locN s "si")) [(locN s "out", 32)] ∧
    memW s (locN s "si" + 16) < 2 ^ 32 ∧
    memW s (memW s (locN s "si") + 56) < 2 ^ 32

theorem wk_htr_new_payload_request_r32 :
    WorldKeeps HtrNewPayloadReadyR32
      (fun s => [(locN s "out", 32),
                 (globN s "ssz_len_chunk", if globN s "ssz_len_chunk" = 0 then 0 else 32)])
      ["heap_ptr"]
      [("ws", [0, 8, 16, 24, 32]), ("bs", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72]),
       ("ts", [0, 8, 16, 24, 32, 40, 48, 56, 64]), ("bo", [0, 8, 16, 24, 32, 40, 48, 56, 64, 72, 80])]
      NoExtra (ofString "htr_new_payload_request") :=
  «wk_htr_new_payload_request_guarded» (fun s h => by
    obtain ⟨⟨S, Nd, hAr, hWT, hcells, hdisj_ow, hnvh', hnwd', hPay, hReq⟩,
      hdisj_out, hnvh, hnwd⟩ := h
    -- The 96-byte run-attempt header cell covers the 40-byte `inputCells` header cell;
    -- its null-pair disjunct is impossible (96 ≠ 0), so it is unconditionally `Inside`.
    have hsi96 := hcells (locN s "si", 96) (by simp [runAttemptCells])
    have hsi96In : Inside (locN s "si", 96) sourceBase (globN s "heap_ptr") := by
      rcases hsi96.2.1 with h | h
      · exact absurd h.2 (by simp)
      · exact h
    have h4 : ∀ i ∈ inputCells s (locN s "si"),
        ((i.1 = 0 ∧ i.2 = 0) ∨ Inside i sourceBase (globN s "heap_ptr")) ∧ WordsOK s i := by
      intro i hi
      rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
      · exact ⟨Or.inr (inside_of_le (by decide) hsi96In),
          wordsOK_of_le (by decide) (by decide) hsi96.2.2⟩
      · exact ⟨(hcells _ (by simp [runAttemptCells])).2.1,
          (hcells _ (by simp [runAttemptCells])).2.2⟩
      · exact ⟨(hcells _ (by simp [runAttemptCells])).2.1,
          (hcells _ (by simp [runAttemptCells])).2.2⟩
      · exact ⟨(hcells _ (by simp [runAttemptCells])).2.1,
          (hcells _ (by simp [runAttemptCells])).2.2⟩
    have hdisj4 : IvlsDisj (inputCells s (locN s "si")) (worldOwned s S Nd) := by
      intro i hi j hj
      rcases inputCells_mem_cases hi with rfl | rfl | rfl | rfl
      · exact disj_left_of_le (by decide : (40 : Nat) ≤ 96)
          (hdisj_ow (locN s "si", 96) (by simp [runAttemptCells]) j hj)
      · exact hdisj_ow _ (by simp [runAttemptCells]) j hj
      · exact hdisj_ow _ (by simp [runAttemptCells]) j hj
      · exact hdisj_ow _ (by simp [runAttemptCells]) j hj
    -- The out-disjunction is stated over the same `inputCells` list in both the
    -- R32 guard and the guarded premise, so it passes through unchanged.
    have hdisj_out4 : IvlsDisj (inputCells s (locN s "si")) [(locN s "out", 32)] := hdisj_out
    exact ⟨hAr, S, Nd, hWT, h4, hdisj4, hdisj_out4, hnvh, hnwd, hPay, hReq⟩)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.WkHtrNewPayloadR32
