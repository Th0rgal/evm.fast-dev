import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryByteWord

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack

def limbWord (value : Limbs256) (j : Nat) : BitVec 64 :=
  if j = 0 then value.l0 else if j = 1 then value.l1 else if j = 2 then value.l2 else value.l3

theorem limbWord_zero_iff (value : Limbs256) :
    value.toNat = 0 ↔ ∀ j : Nat, j < 4 → limbWord value j = 0 := by
  rw [limbs256_zero_iff]
  constructor
  · rintro ⟨h0,h1,h2,h3⟩ j hj
    interval_cases j <;> simp [limbWord, h0,h1,h2,h3]
  · intro h
    exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

theorem memoryU256_limb (memory : BitVec 64 → HolWordLab 64) (base : BitVec 64)
    (value : Limbs256) (hm : MemoryU256 memory base value) (j : Nat) (hj : j < 4) :
    memory (base + BitVec.ofNat 64 (8 * j)) = .word (limbWord value j) := by
  rcases hm with ⟨h0,h1,h2,h3⟩
  interval_cases j
  · simpa [limbWord] using h0
  · exact h1
  · exact h2
  · exact h3

theorem domainU256_limb (domain : BitVec 64 → Prop) (base : BitVec 64)
    (hd : DomainU256 domain base) (j : Nat) (hj : j < 4) :
    domain (base + BitVec.ofNat 64 (8 * j)) := by
  rcases hd with ⟨h0,h1,h2,h3⟩
  interval_cases j
  · simpa [limbWord] using h0
  · exact h1
  · exact h2
  · exact h3

theorem u256_limb_alignment (base : BitVec 64) (j : Nat) (hj : j < 4)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 32 ≤ 2 ^ 64) :
    (base + BitVec.ofNat 64 (8 * j)).toNat % 8 = 0 ∧
    (base + BitVec.ofNat 64 (8 * j)).toNat + 8 ≤ 2 ^ 64 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem byteAddress_decompose (base : BitVec 64) (j k : Nat) :
    (base + BitVec.ofNat 64 (8 * j)) + BitVec.ofNat 64 k =
      base + BitVec.ofNat 64 (8 * j + k) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add]

def u256ByteAt (value : Limbs256) (base : BitVec 64) (be : Bool) (i : Nat) : UInt8 :=
  panGetByteHOL (base + BitVec.ofNat 64 i) (limbWord value (i / 8)) be

theorem memByte_u256 (memory : BitVec 64 → HolWordLab 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (be : Bool)
    (base : BitVec 64) (value : Limbs256)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 32 ≤ 2 ^ 64)
    (hd : DomainU256 domain base) (hm : MemoryU256 memory base value)
    (i : Nat) (hi : i < 32) :
    panMemLoadByteHOL memory domain be (base + BitVec.ofNat 64 i) =
      some (u256ByteAt value base be i) := by
  have hj : i / 8 < 4 := by omega
  have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
  have he : 8 * (i / 8) + i % 8 = i := by omega
  obtain ⟨haj,hbj⟩ := u256_limb_alignment base (i / 8) hj ha hb
  have hh := memByte_word_offset memory domain be (base + BitVec.ofNat 64 (8 * (i / 8)))
    (limbWord value (i / 8)) (i % 8) haj hbj hk
    (domainU256_limb domain base hd _ hj) (memoryU256_limb memory base value hm _ hj)
  simpa only [byteAddress_decompose, he, u256ByteAt] using hh

theorem memByte_zero_iff_u256 (memory : BitVec 64 → HolWordLab 64)
    (domain : BitVec 64 → Prop) [DecidablePred domain] (be : Bool)
    (base : BitVec 64) (value : Limbs256)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 32 ≤ 2 ^ 64)
    (hd : DomainU256 domain base) (hm : MemoryU256 memory base value) :
    (∀ i : Nat, i < 32 → panMemLoadByteHOL memory domain be (base + BitVec.ofNat 64 i) = some 0) ↔
      value.toNat = 0 := by
  rw [limbWord_zero_iff]
  constructor
  · intro h j hj
    obtain ⟨haj,hbj⟩ := u256_limb_alignment base j hj ha hb
    apply (memByte_zero_iff_word memory domain be _ (limbWord value j) haj hbj
      (domainU256_limb domain base hd j hj) (memoryU256_limb memory base value hm j hj)).mp
    intro k hk
    rw [byteAddress_decompose]
    exact h (8*j+k) (by omega)
  · intro h i hi
    have hj : i / 8 < 4 := by omega
    have hk : i % 8 < 8 := Nat.mod_lt _ (by decide)
    have he : 8 * (i / 8) + i % 8 = i := by omega
    obtain ⟨haj,hbj⟩ := u256_limb_alignment base (i / 8) hj ha hb
    have hh := (memByte_zero_iff_word memory domain be _ (limbWord value (i / 8)) haj hbj
      (domainU256_limb domain base hd _ hj) (memoryU256_limb memory base value hm _ hj)).mpr (h _ hj)
    simpa only [byteAddress_decompose, he] using hh (i % 8) hk

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
