import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryColumnRun

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def montAName (i : Fin 8) : MlS :=
  match i.val with
  | 0 => ofString "a0"
  | 1 => ofString "a1"
  | 2 => ofString "a2"
  | 3 => ofString "a3"
  | 4 => ofString "a4"
  | 5 => ofString "a5"
  | 6 => ofString "a6"
  | _ => ofString "a7"

theorem montAName_scratch_free (i : Fin 8) :
    montAName i ≠ ofString "H" ∧ montAName i ≠ ofString "L" ∧
      montAName i ≠ ofString "pr" := by
  fin_cases i <;> decide

def montBName (i : Fin 8) : MlS :=
  match i.val with
  | 0 => ofString "b0"
  | 1 => ofString "b1"
  | 2 => ofString "b2"
  | 3 => ofString "b3"
  | 4 => ofString "b4"
  | 5 => ofString "b5"
  | 6 => ofString "b6"
  | _ => ofString "b7"

theorem montBName_scratch_free (i : Fin 8) :
    montBName i ≠ ofString "H" ∧ montBName i ≠ ofString "L" ∧
      montBName i ≠ ofString "pr" := by
  fin_cases i <;> decide

def montMName (i : Fin 8) : MlS :=
  match i.val with
  | 0 => ofString "m0"
  | 1 => ofString "m1"
  | 2 => ofString "m2"
  | 3 => ofString "m3"
  | 4 => ofString "m4"
  | 5 => ofString "m5"
  | 6 => ofString "m6"
  | _ => ofString "m7"

theorem montMName_scratch_free (i : Fin 8) :
    montMName i ≠ ofString "H" ∧ montMName i ≠ ofString "L" ∧
      montMName i ≠ ofString "pr" := by
  fin_cases i <;> decide

def montUName (i : Fin 7) : MlS :=
  match i.val with
  | 0 => ofString "u0"
  | 1 => ofString "u1"
  | 2 => ofString "u2"
  | 3 => ofString "u3"
  | 4 => ofString "u4"
  | 5 => ofString "u5"
  | _ => ofString "u6"

theorem montUName_scratch_free (i : Fin 7) :
    montUName i ≠ ofString "H" ∧ montUName i ≠ ofString "L" ∧
      montUName i ≠ ofString "pr" := by
  fin_cases i <;> decide

/-- All digit values and scratch-slot types at a column boundary. The
accumulator words are explicit so the same predicate describes its intermediate
product-accumulation state. -/
structure MontSlots {F : Type} (s : PanSemStateFiniteExact 64 F)
    (a b m : Fin 8 → BitVec 64) (u : Fin 7 → BitVec 64)
    (carry low high : BitVec 64) : Prop where
  aWords : ∀ i, s.locals.lookup (montAName i) = some (.val (.word (a i)))
  bWords : ∀ i, s.locals.lookup (montBName i) = some (.val (.word (b i)))
  mWords : ∀ i, s.locals.lookup (montMName i) = some (.val (.word (m i)))
  uWords : ∀ i, s.locals.lookup (montUName i) = some (.val (.word (u i)))
  carryWord : s.locals.lookup (ofString "c") = some (.val (.word carry))
  lowWord : s.locals.lookup (ofString "L") = some (.val (.word low))
  highWord : s.locals.lookup (ofString "H") = some (.val (.word high))
  productWord : ∃ w : BitVec 64, s.locals.lookup (ofString "pr") = some (.val (.word w))
  columnWord : ∃ w : BitVec 64, s.locals.lookup (ofString "col") = some (.val (.word w))
  column2Word : ∃ w : BitVec 64, s.locals.lookup (ofString "col2") = some (.val (.word w))
  digitWord : ∃ w : BitVec 64, s.locals.lookup (ofString "dg") = some (.val (.word w))

/-- Product accumulation preserves all digit locals, the carry and scratch
slot types, while updating the two accumulators to their computed words. -/
theorem montSlots_accumulate {F : Type} {s : PanSemStateFiniteExact 64 F}
    {a b m : Fin 8 → BitVec 64} {u : Fin 7 → BitVec 64} {carry low high : BitVec 64}
    (hs : MontSlots s a b m u carry low high)
    (expressions : List (ExpHOL 64 × ExpHOL 64)) (values : List (BitVec 64 × BitVec 64))
    (hops : List.Forall₂ (fun es vs =>
      MontOperandValue s es.1 vs.1 ∧ MontOperandValue s es.2 vs.2) expressions values) :
    ∃ accumulated, MontAccTrace s expressions accumulated ∧
      MontSlots accumulated a b m u carry
        (montAccWords low high values).1 (montAccWords low high values).2 := by
  obtain ⟨oldPr, hpr⟩ := hs.productWord
  obtain ⟨accumulated, ht, hl', hh'⟩ :=
    montAccTrace_of_operands values s expressions oldPr low high hops hpr hs.lowWord hs.highWord
  refine ⟨accumulated, ht, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, hl', hh', montAccTrace_pr_word ht hs.productWord, ?_, ?_, ?_⟩
  · intro i
    have hf := montAName_scratch_free i
    exact (montAccTrace_lookup_other ht _ hf.1 hf.2.1 hf.2.2).trans (hs.aWords i)
  · intro i
    have hf := montBName_scratch_free i
    exact (montAccTrace_lookup_other ht _ hf.1 hf.2.1 hf.2.2).trans (hs.bWords i)
  · intro i
    have hf := montMName_scratch_free i
    exact (montAccTrace_lookup_other ht _ hf.1 hf.2.1 hf.2.2).trans (hs.mWords i)
  · intro i
    have hf := montUName_scratch_free i
    exact (montAccTrace_lookup_other ht _ hf.1 hf.2.1 hf.2.2).trans (hs.uWords i)
  · exact (montAccTrace_lookup_other ht (ofString "c") (by decide) (by decide) (by decide)).trans hs.carryWord
  · obtain ⟨w, hw⟩ := hs.columnWord
    exact ⟨w, (montAccTrace_lookup_other ht (ofString "col") (by decide) (by decide) (by decide)).trans hw⟩
  · obtain ⟨w, hw⟩ := hs.column2Word
    exact ⟨w, (montAccTrace_lookup_other ht (ofString "col2") (by decide) (by decide) (by decide)).trans hw⟩
  · obtain ⟨w, hw⟩ := hs.digitWord
    exact ⟨w, (montAccTrace_lookup_other ht (ofString "dg") (by decide) (by decide) (by decide)).trans hw⟩

end InitECandidate.Solver.Wave8GuestInv.Arith
