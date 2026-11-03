import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryStep
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryFactors
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryColumnFacts

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- One lower source column, with its numeric equation, bounds, complete
local invariant and runtime code preservation. -/
theorem montLowerStep_bounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry : BitVec 64}
    (hs : MontSlots s a b m u carry 0 0) (dest : String) (i : Fin 8)
    (hdest : ofString dest = montMName i) (products : List (MontFactor × MontFactor))
    (hn : products.length ≤ 16)
    (hp : ∀ p ∈ products, montFactorBounded p.1 ∧ montFactorBounded p.2)
    (ha : ∀ j, (a j).toNat < 2 ^ 32) (hb : ∀ j, (b j).toNat < 2 ^ 32)
    (hm : ∀ j, (m j).toNat < 2 ^ 32) (hc : carry.toNat < 32 * 2 ^ 32)
    (tail : ProgHOL 64) :
    ∃ (digit nextCarry : BitVec 64) (final : PanSemStateFiniteExact 64 F),
      MontSlots final a b (Function.update m i digit) u nextCarry 0 0 ∧
      final.code = s.code ∧
      evaluateHOLFiniteState s (montLowerColumn dest (montFactorExprs products) tail) =
        evaluateHOLFiniteState final tail ∧
      digit.toNat < 2 ^ 32 ∧ nextCarry.toNat < 32 * 2 ^ 32 ∧
      2 ^ 32 * nextCarry.toNat =
        montProductSum (montFactorValues a b m products) + carry.toNat + digit.toNat * 3632069959 := by
  have hvals := montFactorValues_lt a b m products ha hb hm hp
  have hlen : (montFactorValues a b m products).length ≤ 16 := by
    simpa only [montFactorValues, List.length_map] using hn
  have hnum := montLowerProducts_correct (montFactorValues a b m products) carry hlen hvals hc
  obtain ⟨final, hslots, hcode, heval⟩ := montLowerStep hs dest i hdest
    (montFactorExprs products) (montFactorValues a b m products)
    (montFactors_operands hs products) tail
  exact ⟨_, _, final, hslots, hcode, heval, hnum.1, hnum.2.1, hnum.2.2⟩

/-- One upper source column, with its numeric equation, bounds, complete
local invariant and runtime code preservation. -/
theorem montUpperStep_bounded {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry : BitVec 64}
    (hs : MontSlots s a b m u carry 0 0) (dest : String) (i : Fin 7)
    (hdest : ofString dest = montUName i) (products : List (MontFactor × MontFactor))
    (hn : products.length ≤ 16)
    (hp : ∀ p ∈ products, montFactorBounded p.1 ∧ montFactorBounded p.2)
    (ha : ∀ j, (a j).toNat < 2 ^ 32) (hb : ∀ j, (b j).toNat < 2 ^ 32)
    (hm : ∀ j, (m j).toNat < 2 ^ 32) (hc : carry.toNat < 32 * 2 ^ 32)
    (tail : ProgHOL 64) :
    ∃ (digit nextCarry : BitVec 64) (final : PanSemStateFiniteExact 64 F),
      MontSlots final a b m (Function.update u i digit) nextCarry 0 0 ∧
      final.code = s.code ∧
      evaluateHOLFiniteState s (montUpperColumn dest (montFactorExprs products) tail) =
        evaluateHOLFiniteState final tail ∧
      digit.toNat < 2 ^ 32 ∧ nextCarry.toNat < 32 * 2 ^ 32 ∧
      digit.toNat + 2 ^ 32 * nextCarry.toNat =
        montProductSum (montFactorValues a b m products) + carry.toNat := by
  have hvals := montFactorValues_lt a b m products ha hb hm hp
  have hlen : (montFactorValues a b m products).length ≤ 16 := by
    simpa only [montFactorValues, List.length_map] using hn
  have hnum := montUpperProducts_correct (montFactorValues a b m products) carry hlen hvals hc
  obtain ⟨final, hslots, hcode, heval⟩ := montUpperStep hs dest i hdest
    (montFactorExprs products) (montFactorValues a b m products)
    (montFactors_operands hs products) tail
  exact ⟨_, _, final, hslots, hcode, heval, hnum.1, hnum.2.1, hnum.2.2⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
