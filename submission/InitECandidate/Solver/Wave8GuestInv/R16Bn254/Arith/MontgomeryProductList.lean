import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryAccumulate

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Machine-word accumulation of the products in one source column. -/
def montAccWords (low high : BitVec 64) : List (BitVec 64 × BitVec 64) → BitVec 64 × BitVec 64
  | [] => (low, high)
  | (a,b) :: rest =>
      montAccWords (low + montLow32 (a*b)) (high + montHigh32 (a*b)) rest

def montProductSum (products : List (BitVec 64 × BitVec 64)) : Nat :=
  (products.map (fun ab => ab.1.toNat * ab.2.toNat)).sum

/-- Up to sixteen bounded products accumulate without machine-word overflow.
Both the numeric identity and bounds are preserved across the entire list. -/
theorem montAccWords_correct (products : List (BitVec 64 × BitVec 64))
    (n : Nat) (low high : BitVec 64)
    (hn : n + products.length ≤ 16)
    (hl : low.toNat ≤ n * (2 ^ 32 - 1))
    (hh : high.toNat ≤ n * (2 ^ 32 - 1))
    (hp : ∀ ab ∈ products, ab.1.toNat < 2 ^ 32 ∧ ab.2.toNat < 2 ^ 32) :
    (montAccWords low high products).1.toNat ≤ (n + products.length) * (2 ^ 32 - 1) ∧
    (montAccWords low high products).2.toNat ≤ (n + products.length) * (2 ^ 32 - 1) ∧
    (montAccWords low high products).1.toNat +
      2 ^ 32 * (montAccWords low high products).2.toNat =
      low.toNat + 2 ^ 32 * high.toNat + montProductSum products := by
  induction products generalizing n low high with
  | nil => simpa [montAccWords, montProductSum] using And.intro hl hh
  | cons ab rest ih =>
    obtain ⟨a,b⟩ := ab
    have hab := hp (a,b) (by simp)
    have hn' : n < 16 := by simp only [List.length_cons] at hn; omega
    have hbounds := montAccProduct_bounds n low high a b hn' hl hh
    have hl16 : low.toNat ≤ 16 * 2 ^ 32 :=
      (hl.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt hn'))).trans
        (Nat.mul_le_mul_left 16 (Nat.sub_le _ _))
    have hh16 : high.toNat ≤ 16 * 2 ^ 32 :=
      (hh.trans (Nat.mul_le_mul_right _ (Nat.le_of_lt hn'))).trans
        (Nat.mul_le_mul_left 16 (Nat.sub_le _ _))
    have hconserve := montAccProduct_conserve low high a b hl16 hh16 hab.1 hab.2
    have hrest := ih (n+1) (low + montLow32 (a*b)) (high + montHigh32 (a*b))
      (by simp only [List.length_cons] at hn; omega)
      hbounds.1 hbounds.2 (fun cd hcd => hp cd (List.mem_cons_of_mem _ hcd))
    have hlen : n + (rest.length + 1) = n + 1 + rest.length := by omega
    refine ⟨?_, ?_, ?_⟩
    · change (montAccWords (low + montLow32 (a*b))
        (high + montHigh32 (a*b)) rest).1.toNat ≤ (n + (rest.length + 1)) * (2 ^ 32 - 1)
      rw [hlen]
      exact hrest.1
    · change (montAccWords (low + montLow32 (a*b))
        (high + montHigh32 (a*b)) rest).2.toNat ≤ (n + (rest.length + 1)) * (2 ^ 32 - 1)
      rw [hlen]
      exact hrest.2.1
    · change (montAccWords (low + montLow32 (a*b))
        (high + montHigh32 (a*b)) rest).1.toNat +
          2 ^ 32 * (montAccWords (low + montLow32 (a*b))
            (high + montHigh32 (a*b)) rest).2.toNat =
          low.toNat + 2 ^ 32 * high.toNat + (a.toNat * b.toNat + montProductSum rest)
      rw [hrest.2.2, hconserve, Nat.add_assoc]

/-- Updating the scratch accumulators preserves every input/correction digit. -/
theorem montAccState_lookup_other {F : Type} (s : PanSemStateFiniteExact 64 F)
    (low high a b : BitVec 64) (key : MlS)
    (hkH : key ≠ ofString "H") (hkL : key ≠ ofString "L") (hkpr : key ≠ ofString "pr") :
    (montAccState s low high a b).locals.lookup key = s.locals.lookup key := by
  simp [montAccState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
    hkH, hkL, hkpr, Ne.symm hkH, Ne.symm hkL, Ne.symm hkpr]

/-- A finite witness for the actual sequence of product-accumulation blocks.
Every constructor requires operand evaluation and scratch-local typing in the
state in which that product executes. -/
inductive MontAccTrace {F : Type} : PanSemStateFiniteExact 64 F →
    List (ExpHOL 64 × ExpHOL 64) → PanSemStateFiniteExact 64 F → Prop where
  | nil (s) : MontAccTrace s [] s
  | cons {s final} {ae be} {products} (oldPr low high a b : BitVec 64)
      (ha : arithEval s ae = some (.val (.word a)))
      (hb : arithEval s be = some (.val (.word b)))
      (hpr : s.locals.lookup (ofString "pr") = some (.val (.word oldPr)))
      (hl : s.locals.lookup (ofString "L") = some (.val (.word low)))
      (hh : s.locals.lookup (ofString "H") = some (.val (.word high)))
      (rest : MontAccTrace (montAccState s low high a b) products final) :
      MontAccTrace s ((ae,be) :: products) final

theorem montAccProducts_eval_of_trace {F : Type} {s final : PanSemStateFiniteExact 64 F}
    {products : List (ExpHOL 64 × ExpHOL 64)} (h : MontAccTrace s products final)
    (tail : ProgHOL 64) :
    evaluateHOLFiniteState s (montAccProducts products tail) = evaluateHOLFiniteState final tail := by
  induction h with
  | nil => rfl
  | cons oldPr low high a b ha hb hpr hl hh rest ih =>
    change evaluateHOLFiniteState _ (montAccProduct _ _ (montAccProducts _ tail)) = _
    rw [montAccProduct_eval _ _ _ _ oldPr low high a b ha hb hpr hl hh]
    exact ih

end InitECandidate.Solver.Wave8GuestInv.Arith
