import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeProbeValues
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MemoryPolynomial

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def DomainPolynomial (domain : BitVec 64 → Prop) (base : BitVec 64) : Prop :=
  ∀ j, j < 13 → DomainU256 domain (coefficientAddress base j)

theorem coefficientAddress_source (base : BitVec 64) (j : Nat) :
    base + BitVec.ofNat 64 j * 32 = coefficientAddress base j := by
  change base + BitVec.ofNat 64 j * BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_mul]
  simp only [coefficientAddress, Nat.mul_comm]

theorem coefficientAddress_alignment (base : BitVec 64) (j : Nat) (hj : j < 13)
    (ha : base.toNat % 8 = 0) (hb : base.toNat + 416 ≤ 2 ^ 64) :
    (coefficientAddress base j).toNat % 8 = 0 ∧
    (coefficientAddress base j).toNat + 32 ≤ 2 ^ 64 := by
  simp only [coefficientAddress, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem degreeIndex_decrement (n : Nat) (hpos : 0 < n) (hn : n ≤ 13) :
    BitVec.ofNat 64 n - 1 = BitVec.ofNat 64 (n - 1) := by
  exact BitVec.ofNat_sub_ofNat_of_le n 1 (by decide) hpos

theorem fqDegreeBody_memoryPure : MemoryPure fqDegreeBody := by
  apply memoryPure_of_syntax (fun n => decide (n = ofString "is_zero_bytes"))
  · intro n hn
    have he : n = ofString "is_zero_bytes" := of_decide_eq_true hn
    subst n
    exact zeroBytes_function_memoryPure
  · decide

theorem fqDegreeBody_nonzero {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (base : BitVec 64) (coefficients : Nat → Limbs256) (n : Nat) (ret : ValueHOL 64)
    (hpos : 0 < n) (hn : n ≤ 13) (hc : s.code = originalRuntimeCode)
    (ha : s.locals.lookup (ofString "a") = some (.val (.word base)))
    (hi : s.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 n))))
    (halign : base.toNat % 8 = 0) (hbound : base.toNat + 416 ≤ 2 ^ 64)
    (hd : DomainPolynomial s.memaddrs base) (hm : MemoryPolynomial s.memory base coefficients)
    (hr : evaluateHOLFiniteState s fqDegreeBody = (some (.returned ret), post)) :
    (coefficients (n - 1)).toNat ≠ 0 := by
  unfold fqDegreeBody at hr
  rw [evaluateHOLFiniteState_seq_line780, fqDegree_decrement s (BitVec.ofNat 64 n) hi,
    degreeIndex_decrement n hpos hn] at hr
  let next := setVarHOLFinite (ofString "i") (.val (.word (BitVec.ofNat 64 (n - 1)))) s
  have ha' : next.locals.lookup (ofString "a") = some (.val (.word base)) := by
    simpa [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
      show ofString "i" ≠ ofString "a" by decide] using ha
  have hi' : next.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 (n - 1)))) := by
    simp [next, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  have hj : n - 1 < 13 := by omega
  obtain ⟨haj,hbj⟩ := coefficientAddress_alignment base (n-1) hj halign hbound
  apply fqDegreeProbe_returned_nonzero next post base (BitVec.ofNat 64 (n-1))
    (coefficients (n-1)) ret hc ha' hi'
  · simpa only [coefficientAddress_source] using haj
  · simpa only [coefficientAddress_source] using hbj
  · simpa only [coefficientAddress_source, next, setVarHOLFinite] using hd (n-1) hj
  · simpa only [coefficientAddress_source, next, setVarHOLFinite] using hm (n-1) hj
  · exact hr

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
