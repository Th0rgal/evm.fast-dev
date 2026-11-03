import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryByteZero

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack

theorem memByte_word_offset (memory : BitVec 64 → HolWordLab 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (be : Bool)
    (base word : BitVec 64) (i : Nat)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 8 ≤ 2 ^ 64) (hi : i < 8)
    (hd : domain base) (hm : memory base = .word word) :
    panMemLoadByteHOL memory domain be (base + BitVec.ofNat 64 i) =
      some (panGetByteHOL (base + BitVec.ofNat 64 i) word be) := by
  simp only [panMemLoadByteHOL, byteAlign_word_offset base i ha hb hi, hm, if_pos hd]

theorem memByte_zero_iff_word (memory : BitVec 64 → HolWordLab 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (be : Bool)
    (base word : BitVec 64)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 8 ≤ 2 ^ 64)
    (hd : domain base) (hm : memory base = .word word) :
    (∀ i : Nat, i < 8 → panMemLoadByteHOL memory domain be (base + BitVec.ofNat 64 i) = some 0) ↔
      word = 0 := by
  rw [← getByte_zero_iff_word base word be ha hb]
  constructor
  · intro h i hi
    have hh := h i hi
    rw [memByte_word_offset memory domain be base word i ha hb hi hd hm] at hh
    exact congrArg UInt8.toNat (Option.some.inj hh)
  · intro h i hi
    rw [memByte_word_offset memory domain be base word i ha hb hi hd hm]
    apply congrArg some
    apply UInt8.toNat_inj.mp
    exact h i hi

end InitECandidate.Solver.Wave8GuestInv.Arith
