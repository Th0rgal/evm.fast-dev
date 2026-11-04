import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryProductList

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

/-- All actual column operands are constants or locals distinct from the three
accumulation scratch slots. This witness records their values in the initial state. -/
inductive MontOperandValue {F : Type} (s : PanSemStateFiniteExact 64 F) :
    ExpHOL 64 → BitVec 64 → Prop where
  | const (w : BitVec 64) : MontOperandValue s (.const w) w
  | localValue (key : MlS) (w : BitVec 64)
      (hkH : key ≠ ofString "H") (hkL : key ≠ ofString "L")
      (hkpr : key ≠ ofString "pr")
      (hv : s.locals.lookup key = some (.val (.word w))) :
      MontOperandValue s (.var .local key) w

theorem montOperandValue_eval {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {w : BitVec 64} (h : MontOperandValue s e w) :
    arithEval s e = some (.val (.word w)) := by
  cases h with
  | const => rfl
  | localValue key w hkH hkL hkpr hv => exact hv

theorem montOperandValue_acc {F : Type} {s : PanSemStateFiniteExact 64 F}
    {e : ExpHOL 64} {w : BitVec 64} (h : MontOperandValue s e w)
    (low high a b : BitVec 64) :
    MontOperandValue (montAccState s low high a b) e w := by
  cases h with
  | const => exact .const _
  | localValue key w hkH hkL hkpr hv =>
    apply MontOperandValue.localValue key w hkH hkL hkpr
    rw [montAccState_lookup_other s low high a b key hkH hkL hkpr]
    exact hv

/-- Accumulating a column leaves all non-scratch locals unchanged. -/
theorem montAccTrace_lookup_other {F : Type} {s final : PanSemStateFiniteExact 64 F}
    {expressions : List (ExpHOL 64 × ExpHOL 64)} (h : MontAccTrace s expressions final)
    (key : MlS) (hkH : key ≠ ofString "H") (hkL : key ≠ ofString "L")
    (hkpr : key ≠ ofString "pr") :
    final.locals.lookup key = s.locals.lookup key := by
  induction h with
  | nil => rfl
  | cons oldPr low high a b ha hb hpr hl hh rest ih =>
    exact ih.trans (montAccState_lookup_other _ low high a b key hkH hkL hkpr)

/-- Static operand witnesses construct the evaluator trace and identify its
final accumulator words. The caller still supplies digit bounds for arithmetic. -/
theorem montAccTrace_of_operands {F : Type}
    (values : List (BitVec 64 × BitVec 64))
    (s : PanSemStateFiniteExact 64 F) (expressions : List (ExpHOL 64 × ExpHOL 64))
    (oldPr low high : BitVec 64)
    (hops : List.Forall₂ (fun es vs =>
      MontOperandValue s es.1 vs.1 ∧ MontOperandValue s es.2 vs.2) expressions values)
    (hpr : s.locals.lookup (ofString "pr") = some (.val (.word oldPr)))
    (hl : s.locals.lookup (ofString "L") = some (.val (.word low)))
    (hh : s.locals.lookup (ofString "H") = some (.val (.word high))) :
    ∃ final, MontAccTrace s expressions final ∧
      final.locals.lookup (ofString "L") = some (.val (.word (montAccWords low high values).1)) ∧
      final.locals.lookup (ofString "H") = some (.val (.word (montAccWords low high values).2)) := by
  induction values generalizing s expressions oldPr low high with
  | nil =>
    cases hops
    exact ⟨s, .nil s, hl, hh⟩
  | cons ab rest ih =>
    cases hops with
    | cons hop hrest =>
      obtain ⟨a,b⟩ := ab
      have hrest' := hrest.imp (fun _ _ h =>
        And.intro (montOperandValue_acc h.1 low high a b)
          (montOperandValue_acc h.2 low high a b))
      have hpr' : (montAccState s low high a b).locals.lookup (ofString "pr") =
          some (.val (.word (a*b))) := by
        simp [montAccState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "pr" ≠ ofString "H" by decide,
          show ofString "pr" ≠ ofString "L" by decide,
          show ofString "H" ≠ ofString "pr" by decide,
          show ofString "L" ≠ ofString "pr" by decide]
      have hl' : (montAccState s low high a b).locals.lookup (ofString "L") =
          some (.val (.word (low + montLow32 (a*b)))) := by
        simp [montAccState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE,
          show ofString "L" ≠ ofString "H" by decide,
          show ofString "H" ≠ ofString "L" by decide]
      have hh' : (montAccState s low high a b).locals.lookup (ofString "H") =
          some (.val (.word (high + montHigh32 (a*b)))) := by
        simp [montAccState, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
      obtain ⟨final, ht, hfl, hfh⟩ := ih (montAccState s low high a b) _ (a*b)
        (low + montLow32 (a*b)) (high + montHigh32 (a*b)) hrest' hpr' hl' hh'
      exact ⟨final, .cons oldPr low high a b (montOperandValue_eval hop.1)
        (montOperandValue_eval hop.2) hpr hl hh ht, hfl, hfh⟩

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
