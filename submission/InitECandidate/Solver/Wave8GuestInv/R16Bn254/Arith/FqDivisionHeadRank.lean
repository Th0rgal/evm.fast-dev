import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolynomialRank
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqStationaryRank
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionSource

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Read the active degree, leading coefficient and current quotient slot from
machine state. Malformed or out-of-range degrees receive zero rank. -/
def divisionHeadRank {F : Type} (s : PanSemStateFiniteExact 64 F) : Nat :=
  match s.locals.lookup (ofString "r0"), s.locals.lookup (ofString "q"),
    s.locals.lookup (ofString "d0"), s.locals.lookup (ofString "d1") with
  | some (.val (.word a)),some (.val (.word q)),some (.val (.word d0)),some (.val (.word d1)) =>
      if d0.toNat < 13 then
        divisionStationaryRank d0.toNat
          (polynomialMemoryCoefficients s.memory a d0.toNat).toNat
          (polynomialMemoryCoefficients s.memory q (d0.toNat-d1.toNat)).toNat
      else 0
  | _,_,_,_ => 0

theorem divisionHeadRank_bound {F : Type} (s : PanSemStateFiniteExact 64 F) :
    divisionHeadRank s ≤ 14 := by
  unfold divisionHeadRank
  split
  · split
    · exact divisionStationaryRank_le14 _ _ _ (by assumption)
    · omega
  · omega

theorem polynomialMemoryCoefficient_read (memory : BitVec 64 → HolWordLab 64)
    (base : BitVec 64) (j : Nat) (v : Limbs256)
    (hm : MemoryU256 memory (coefficientAddress base j) v) :
    polynomialMemoryCoefficients memory base j = v := by
  rcases hm with ⟨h0,h1,h2,h3⟩
  cases v
  simp_all [polynomialMemoryCoefficients,polynomialMemoryWord]

theorem divisionHeadRank_represented {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b q : BitVec 64) (d0 d1 : Nat) (top slot : Limbs256)
    (h0 : d0 < 13) (h1 : d1 < 13) (hl : PolyDivLocals s.locals a b q d0 d1)
    (ht : MemoryU256 s.memory (coefficientAddress a d0) top)
    (hs : MemoryU256 s.memory (coefficientAddress q (d0-d1)) slot) :
    divisionHeadRank s = divisionStationaryRank d0 top.toNat slot.toNat := by
  have h064 : d0 < 2^64 := by omega
  have h164 : d1 < 2^64 := by omega
  simp only [divisionHeadRank,hl.r0,hl.q,hl.degree0,hl.degree1,
    BitVec.toNat_ofNat,Nat.mod_eq_of_lt h064,Nat.mod_eq_of_lt h164,if_pos h0]
  rw [polynomialMemoryCoefficient_read s.memory a d0 top ht,
    polynomialMemoryCoefficient_read s.memory q (d0-d1) slot hs]

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
