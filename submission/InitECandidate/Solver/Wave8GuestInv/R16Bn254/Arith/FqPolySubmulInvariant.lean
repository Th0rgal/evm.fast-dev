import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolySubmulBody
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqDegreeMemory
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialStore

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup

def PolynomialDisjoint (a b : BitVec 64) : Prop :=
  ∀ j, j < 13 → ∀ k, k < 13 → ∀ x ∈ u256Addresses (coefficientAddress b k),
    x ∉ u256Addresses (coefficientAddress a j)

def PolynomialOutside (a x : BitVec 64) : Prop :=
  ∀ j, j < 13 → x ∉ u256Addresses (coefficientAddress a j)

def PolynomialFrame (before after : BitVec 64 → HolWordLab 64) (base : BitVec 64) : Prop :=
  ∀ x, PolynomialOutside base x → after x = before x

def SubmulCoefficient (q A B out : Limbs256) : Prop :=
  ∃ product : Nat, product < fqModulus.toNat ∧ out.toNat < fqModulus.toNat ∧
    Nat.ModEq fqModulus.toNat (2^256*product) (q.toNat*B.toNat) ∧
    Nat.ModEq fqModulus.toNat (out.toNat+product) A.toNat

theorem writeCoefficient_disjoint (memory : BitVec 64 → HolWordLab 64)
    (a b : BitVec 64) (B : Nat → Limbs256) (j : Nat) (out : Limbs256)
    (hj : j < 13) (hsep : PolynomialDisjoint a b) (hm : MemoryPolynomial memory b B) :
    MemoryPolynomial (writeU256 memory (coefficientAddress a j) out) b B := by
  intro k hk
  exact writeU256_preserves memory _ _ out (B k) (hsep j hj k hk) (hm k hk)

theorem writeCoefficient_frame (memory : BitVec 64 → HolWordLab 64)
    (base : BitVec 64) (j : Nat) (out : Limbs256) (hj : j < 13) :
    PolynomialFrame memory (writeU256 memory (coefficientAddress base j) out) base := by
  intro x hx
  exact writeU256_frame memory _ x out (hx j hj)

theorem coefficientAddress_shift (a : BitVec 64) (shift i : Nat) :
    a+(BitVec.ofNat 64 shift+BitVec.ofNat 64 i)*32 = coefficientAddress a (shift+i) := by
  rw [← BitVec.ofNat_add,coefficientAddress_source]

/-- One actual iteration preserves both represented polynomials and updates
exactly the intended destination coefficient, preserving all outside memory. -/
theorem polySubmulBody_polynomial {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b : BitVec 64) (shift i : Nat) (A B : Nat → Limbs256) (q : Limbs256)
    (hiBound : i < 13) (htarget : shift+i < 13)
    (hc : state.code = originalRuntimeCode)
    (ha : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (hb : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (hs : state.locals.lookup (ofString "s") = some (.val (.word (BitVec.ofNat 64 shift))))
    (hi : state.locals.lookup (ofString "i") = some (.val (.word (BitVec.ofNat 64 i))))
    (hq : state.locals.lookup (ofString "q") = some q.toValue)
    (hACanon : CanonicalPolynomial A) (hBCanon : CanonicalPolynomial B)
    (hdA : DomainPolynomial state.memaddrs a) (hdB : DomainPolynomial state.memaddrs b)
    (hmA : MemoryPolynomial state.memory a A) (hmB : MemoryPolynomial state.memory b B)
    (hsep : PolynomialDisjoint a b)
    (hr : evaluateHOLFiniteState state polySubmulBody = (none,post)) :
    ∃ out : Limbs256,
      SubmulCoefficient q (A (shift+i)) (B i) out ∧
      MemoryPolynomial post.memory a (fun j => if j = shift+i then out else A j) ∧
      CanonicalPolynomial (fun j => if j = shift+i then out else A j) ∧
      MemoryPolynomial post.memory b B ∧ PolynomialFrame state.memory post.memory a := by
  have hdA' : DomainU256 state.memaddrs (a+(BitVec.ofNat 64 shift+BitVec.ofNat 64 i)*32) := by
    rw [coefficientAddress_shift]; exact hdA (shift+i) htarget
  have hdB' : DomainU256 state.memaddrs (b+BitVec.ofNat 64 i*32) := by
    rw [coefficientAddress_source]; exact hdB i hiBound
  have hmA' : MemoryU256 state.memory (a+(BitVec.ofNat 64 shift+BitVec.ofNat 64 i)*32) (A (shift+i)) := by
    rw [coefficientAddress_shift]; exact hmA (shift+i) htarget
  have hmB' : MemoryU256 state.memory (b+BitVec.ofNat 64 i*32) (B i) := by
    rw [coefficientAddress_source]; exact hmB i hiBound
  obtain ⟨product,out,hprodCanon,houtCanon,hprod,hsub,hwrite⟩ := polySubmulBody_none state post
    a b (BitVec.ofNat 64 shift) (BitVec.ofNat 64 i) (A (shift+i)) (B i) q
    hc ha hb hs hi hq (hACanon _ htarget) (hBCanon _ hiBound) hdA' hdB' hmA' hmB' hr
  rw [coefficientAddress_shift] at hwrite
  refine ⟨out,⟨product.toNat,hprodCanon,houtCanon,hprod,hsub⟩,?_,?_,?_,?_⟩
  · rw [hwrite]
    exact writeCoefficient_polynomial state.memory a A (shift+i) out htarget hmA
  · exact canonicalPolynomial_update A (shift+i) out hACanon houtCanon
  · rw [hwrite]
    exact writeCoefficient_disjoint state.memory a b B (shift+i) out htarget hsep hmB
  · rw [hwrite]
    exact writeCoefficient_frame state.memory a (shift+i) out htarget

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
