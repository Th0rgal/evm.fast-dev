import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomerySlots

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
open InitECandidate.Solver.Wave8GuestInv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Operand forms that occur in the actual fq_mul columns. -/
inductive MontFactor where
  | a (i : Fin 8)
  | b (i : Fin 8)
  | m (i : Fin 8)
  | constant (word : BitVec 64)

def montFactorExpr : MontFactor → ExpHOL 64
  | .a i => .var .local (montAName i)
  | .b i => .var .local (montBName i)
  | .m i => .var .local (montMName i)
  | .constant word => .const word

def montFactorValue (a b m : Fin 8 → BitVec 64) : MontFactor → BitVec 64
  | .a i => a i
  | .b i => b i
  | .m i => m i
  | .constant word => word

def montFactorBounded : MontFactor → Prop
  | .constant word => word.toNat < 2 ^ 32
  | _ => True

def montFactorExprs (products : List (MontFactor × MontFactor)) : List (ExpHOL 64 × ExpHOL 64) :=
  products.map (fun p => (montFactorExpr p.1, montFactorExpr p.2))

def montFactorValues (a b m : Fin 8 → BitVec 64)
    (products : List (MontFactor × MontFactor)) : List (BitVec 64 × BitVec 64) :=
  products.map (fun p => (montFactorValue a b m p.1, montFactorValue a b m p.2))

theorem montFactor_operand {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry low high : BitVec 64}
    (hs : MontSlots s a b m u carry low high) (factor : MontFactor) :
    MontOperandValue s (montFactorExpr factor) (montFactorValue a b m factor) := by
  cases factor with
  | a i =>
    have hf := montAName_scratch_free i
    exact .localValue _ _ hf.1 hf.2.1 hf.2.2 (hs.aWords i)
  | b i =>
    have hf := montBName_scratch_free i
    exact .localValue _ _ hf.1 hf.2.1 hf.2.2 (hs.bWords i)
  | m i =>
    have hf := montMName_scratch_free i
    exact .localValue _ _ hf.1 hf.2.1 hf.2.2 (hs.mWords i)
  | constant word => exact .const word

theorem montFactors_operands {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry low high : BitVec 64}
    (hs : MontSlots s a b m u carry low high) (products : List (MontFactor × MontFactor)) :
    List.Forall₂ (fun es vs => MontOperandValue s es.1 vs.1 ∧ MontOperandValue s es.2 vs.2)
      (montFactorExprs products) (montFactorValues a b m products) := by
  induction products with
  | nil => exact .nil
  | cons product rest ih =>
    exact .cons ⟨montFactor_operand hs product.1, montFactor_operand hs product.2⟩ ih

theorem montFactorValue_lt (a b m : Fin 8 → BitVec 64) (factor : MontFactor)
    (ha : ∀ i, (a i).toNat < 2 ^ 32) (hb : ∀ i, (b i).toNat < 2 ^ 32)
    (hm : ∀ i, (m i).toNat < 2 ^ 32) (hf : montFactorBounded factor) :
    (montFactorValue a b m factor).toNat < 2 ^ 32 := by
  cases factor with
  | a i => exact ha i
  | b i => exact hb i
  | m i => exact hm i
  | constant word => exact hf

theorem montFactorValues_lt (a b m : Fin 8 → BitVec 64)
    (products : List (MontFactor × MontFactor))
    (ha : ∀ i, (a i).toNat < 2 ^ 32) (hb : ∀ i, (b i).toNat < 2 ^ 32)
    (hm : ∀ i, (m i).toNat < 2 ^ 32)
    (hp : ∀ p ∈ products, montFactorBounded p.1 ∧ montFactorBounded p.2) :
    ∀ ab ∈ montFactorValues a b m products, ab.1.toNat < 2 ^ 32 ∧ ab.2.toNat < 2 ^ 32 := by
  intro ab hab
  obtain ⟨p, hmem, rfl⟩ := List.mem_map.mp hab
  exact ⟨montFactorValue_lt a b m p.1 ha hb hm (hp p hmem).1,
    montFactorValue_lt a b m p.2 ha hb hm (hp p hmem).2⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
