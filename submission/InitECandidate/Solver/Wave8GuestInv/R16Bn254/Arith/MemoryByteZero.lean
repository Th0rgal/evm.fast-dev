import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryU256
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256ZeroSemantics

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack

/-- Byte access within a nonwrapping aligned word selects that word. -/
theorem byteAlign_word_offset (base : BitVec 64) (i : Nat)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 8 ≤ 2 ^ 64) (hi : i < 8) :
    panByteAlignHOL (base + BitVec.ofNat 64 i) = base := by
  apply BitVec.toNat_inj.mp
  rw [byteAlign_toNat]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem byteIndex_word_offset (base : BitVec 64) (i : Nat)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 8 ≤ 2 ^ 64) (hi : i < 8) :
    (base + BitVec.ofNat 64 i).toNat % 8 = i := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem word64_zero_iff_digits (word : BitVec 64) :
    word = 0 ↔ ∀ i : Nat, i < 8 → word.toNat / 256 ^ i % 256 = 0 := by
  constructor
  · intro hz i hi
    simp [hz]
  · intro h
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    have h6 := h 6 (by decide)
    have h7 := h 7 (by decide)
    norm_num at h0 h1 h2 h3 h4 h5 h6 h7
    apply BitVec.toNat_inj.mp
    have hw := word.isLt
    change word.toNat = 0
    omega

theorem getByte_word_offset (base word : BitVec 64) (i : Nat) (be : Bool)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 8 ≤ 2 ^ 64) (hi : i < 8) :
    (panGetByteHOL (base + BitVec.ofNat 64 i) word be).toNat =
      word.toNat / 256 ^ (if be then 7 - i else i) % 256 := by
  unfold panGetByteHOL
  simp only [show 64 / 8 = 8 from rfl, byteIndex_word_offset base i ha hb hi]
  simp

theorem getByte_zero_iff_word (base word : BitVec 64) (be : Bool)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 8 ≤ 2 ^ 64) :
    (∀ i : Nat, i < 8 → (panGetByteHOL (base + BitVec.ofNat 64 i) word be).toNat = 0) ↔
      word = 0 := by
  constructor
  · intro h
    apply word64_zero_iff_digits word |>.mpr
    intro i hi
    cases be with
    | false => simpa [getByte_word_offset base word i false ha hb hi] using h i hi
    | true =>
        have hj : 7 - i < 8 := by omega
        have he : 7 - (7 - i) = i := by omega
        simpa [getByte_word_offset base word (7 - i) true ha hb hj, he] using h (7 - i) hj
  · intro hz i hi
    rw [getByte_word_offset base word i be ha hb hi, hz]
    simp

end InitECandidate.Solver.Wave8GuestInv.Arith
