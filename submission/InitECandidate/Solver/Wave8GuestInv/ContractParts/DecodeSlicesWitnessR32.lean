import InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32
import InitECandidate.Solver.Wave8GuestInv.R16Shards.EvmEkFk.StorageCreateFinish

/-!
# `decode_bytes_list` produces `WitnessSliceOK` slices (R32)

`WitnessSliceOK` is the per-slice fact `nodedb_build` needs
(`NodeDbSlicesReady`, hence `NodeDbSlicesBounded` / `wsi`).  With the slice
posts of `DecodeSlicesR32` it follows for every slice returned by
`decode_bytes_list`, provided the list being split lies in the heap below the
entry `heap_ptr` and is shorter than `2 ^ 40` bytes.  Both provisos hold for a
list cut out of the `input_blob` allocation (`input_blob_body_returns_heap`),
but threading them through `decode_stateless_input` is not done here.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option exponentiation.threshold 2000
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

/-- One slice cell of a slice array is `WitnessSliceOK` as soon as the array is
in the heap and the slice lies inside a heap region `[p, p + len)`. -/
theorem witnessSliceOK_of_slice {F : Type} (s : PanSemStateFiniteExact 64 F)
    (arr cnt p len j : Nat)
    (hwok : WordsOK s (arr, 16 * cnt))
    (harr_sb : sourceBase ≤ arr) (harr_hi : arr + 16 * cnt ≤ globN s "heap_ptr")
    (hp_sb : sourceBase ≤ p) (hp_hi : p + len ≤ globN s "heap_ptr")
    (hhp : globN s "heap_ptr" < 2 ^ 64) (hlen : len < 2 ^ 40) (hj : j < cnt)
    (hptr : ∃ o : Nat, memW s (arr + 16 * j) = (p + o) % 2 ^ 64 ∧
      o + memW s (arr + 16 * j + 8) ≤ len) :
    WitnessSliceOK s (arr + 16 * j) := by
  obtain ⟨o, ho1, ho2⟩ := hptr
  have harr_al : arr % 8 = 0 := hwok.1
  have hptr_eq : memW s (arr + 16 * j) = p + o := by
    rw [ho1]; exact Nat.mod_eq_of_lt (by omega)
  refine ⟨⟨?_, (by show 16 % 8 = 0; decide), fun k hk => ?_⟩, ⟨?_, ?_⟩, by omega, ⟨?_, ?_⟩⟩
  · show (arr + 16 * j) % 8 = 0
    omega
  · have hk' : k < 16 / 8 := hk
    have h := hwok.2.2 (2 * j + k) (by show 2 * j + k < 16 * cnt / 8; omega)
    have e : arr + 8 * (2 * j + k) = arr + 16 * j + 8 * k := by omega
    rw [← e]; exact h
  · show sourceBase ≤ arr + 16 * j
    omega
  · show arr + 16 * j + 16 ≤ globN s "heap_ptr"
    omega
  · show sourceBase ≤ memW s (arr + 16 * j)
    omega
  · show memW s (arr + 16 * j) + memW s (arr + 16 * j + 8) ≤ globN s "heap_ptr"
    omega

/-- `decode_bytes_list` on a list inside the heap (below the entry `heap_ptr`)
returns an array all of whose slices are `WitnessSliceOK`. -/
theorem decode_bytes_list_witnessSliceOK {F : Type}
    {s entry post : PanSemStateFiniteExact 64 F} {Rl : List Ivl} {B : List (String × Nat)}
    {wp wlen wlim wmaxb : BitVec 64} {rv : ValueHOL 64}
    (heff : WorldEff s entry Rl B dhiGw)
    (hp : entry.locals.lookup (ofString "p") = some (.val (.word wp)))
    (hlen : entry.locals.lookup (ofString "len") = some (.val (.word wlen)))
    (hlim : entry.locals.lookup (ofString "lim") = some (.val (.word wlim)))
    (hmaxb : entry.locals.lookup (ofString "maxb") = some (.val (.word wmaxb)))
    (hrun : evaluateHOLFiniteState entry (sourceFnBody Guest.Software.guestFn_decode_bytes_list) =
      (some (.returned rv), post))
    (hp_sb : sourceBase ≤ wp.toNat)
    (hp_hi : wp.toNat + wlen.toNat ≤ globN entry "heap_ptr")
    (hlen40 : wlen.toNat < 2 ^ 40) :
    ∃ (w_arr w_cnt : BitVec 64),
      rv = .rStruct [.val (.word w_arr), .val (.word w_cnt)] ∧
      ∀ j : Nat, j < w_cnt.toNat → WitnessSliceOK post (w_arr.toNat + 16 * j) := by
  obtain ⟨_, _, w_arr, w_cnt, hrv, _, _, _, hwok, hcases⟩ :=
    decode_bytes_list_body_returns_slices heff hp hlen hlim hmaxb hrun
  refine ⟨w_arr, w_cnt, hrv, fun j hj => ?_⟩
  rcases hcases with ⟨h0, _, _⟩ | ⟨_, harr_sb, harr_lo, harr_hi, hhp_lim, _, hsl⟩
  · omega
  · have hhl : heapLimit < 2 ^ 64 := by decide
    exact witnessSliceOK_of_slice post w_arr.toNat w_cnt.toNat wp.toNat wlen.toNat j hwok harr_sb harr_hi
      hp_sb (by omega) (by omega) hlen40 hj (hsl j hj)

end InitECandidate.Solver.Wave8GuestInv.ContractParts.DecodeSlicesR32
