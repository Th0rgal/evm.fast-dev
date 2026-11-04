import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryStoreFrame
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.U256Arithmetic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The four words used by the actual U256 load, with machine-word addresses. -/
def MemoryU256 (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64)
    (value : Limbs256) : Prop :=
  memory address = .word value.l0 ∧
  memory (address + 8) = .word value.l1 ∧
  memory (address + 16) = .word value.l2 ∧
  memory (address + 24) = .word value.l3

def DomainU256 (domain : BitVec 64 → Prop) (address : BitVec 64) : Prop :=
  domain address ∧ domain (address + 8) ∧ domain (address + 16) ∧ domain (address + 24)

/-- Explicit value of the actual four sequential machine-word writes. -/
def writeU256 (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64)
    (value : Limbs256) : BitVec 64 → HolWordLab 64 := fun x =>
  if x = address + 24 then .word value.l3 else
  if x = address + 16 then .word value.l2 else
  if x = address + 8 then .word value.l1 else
  if x = address then .word value.l0 else memory x

theorem limbs256_flatten (value : Limbs256) :
    flattenHOL value.toValue = [.word value.l0, .word value.l1, .word value.l2, .word value.l3] := by
  simp [Limbs256.toValue, flattenHOL]

theorem memLoad_u256 (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64)
    (value : Limbs256) (domain : BitVec 64 → Prop) [DecidablePred domain]
    (context : StructContextHOLM) (hd : DomainU256 domain address)
    (hv : MemoryU256 memory address value) :
    memLoadHOLExact (.comb [.one, .one, .one, .one]) address domain memory context =
      some value.toValue := by
  rcases hd with ⟨h0,h1,h2,h3⟩
  rcases hv with ⟨v0,v1,v2,v3⟩
  change domain (address + 8#64) at h1
  change domain (address + 16#64) at h2
  change domain (address + 24#64) at h3
  change memory (address + 8#64) = .word value.l1 at v1
  change memory (address + 16#64) = .word value.l2 at v2
  change memory (address + 24#64) = .word value.l3 at v3
  simp [memLoadHOLExact, memLoadsHOLExact, sizeOfShapeWithContextHOL,
    bytesInWordHOL, BitVec.add_assoc, h0,h1,h2,h3,v0,v1,v2,v3,Limbs256.toValue]

theorem memStore_u256 (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64)
    (value : Limbs256) (domain : BitVec 64 → Prop) [DecidablePred domain]
    (hd : DomainU256 domain address) :
    panMemStoresHOL address (flattenHOL value.toValue) domain memory =
      some (writeU256 memory address value) := by
  rcases hd with ⟨h0,h1,h2,h3⟩
  change domain (address + 8#64) at h1
  change domain (address + 16#64) at h2
  change domain (address + 24#64) at h3
  simp [limbs256_flatten, panMemStoresHOL, panMemStoreHOL, panBytesInWord,
    BitVec.add_assoc, h0,h1,h2,h3]
  rfl

theorem writeU256_value (memory : BitVec 64 → HolWordLab 64) (address : BitVec 64)
    (value : Limbs256) : MemoryU256 (writeU256 memory address value) address value := by
  simp [MemoryU256, writeU256, BitVec.add_left_inj]

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
