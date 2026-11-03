import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.MontgomeryInitWords
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqInputDigits

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

inductive FqInitFactor where
  | a (i : Fin 8)
  | b (i : Fin 8)
  | zero

def fqInitExpr : FqInitFactor → ExpHOL 64
  | .a i => fqInputWordExpr (ofString "a") i
  | .b i => fqInputWordExpr (ofString "b") i
  | .zero => .const 0

def fqInitValue (A B : Limbs256) : FqInitFactor → BitVec 64
  | .a i => limbs256Words A i
  | .b i => limbs256Words B i
  | .zero => 0

def fqInitExpressions (specs : List (String × FqInitFactor)) : List (String × ExpHOL 64) :=
  specs.map (fun ne => (ne.1, fqInitExpr ne.2))

def fqInitAssignments (A B : Limbs256) (specs : List (String × FqInitFactor)) :
    List (String × BitVec 64) := specs.map (fun ne => (ne.1, fqInitValue A B ne.2))

theorem fqInitFactor_eval {F : Type} (s : PanSemStateFiniteExact 64 F) (A B : Limbs256)
    (ha : s.locals.lookup (ofString "a") = some A.toValue)
    (hb : s.locals.lookup (ofString "b") = some B.toValue) (factor : FqInitFactor) :
    arithEval s (fqInitExpr factor) = some (.val (.word (fqInitValue A B factor))) := by
  cases factor with
  | a i => exact fqInputWordExpr_eval s _ A i ha
  | b i => exact fqInputWordExpr_eval s _ B i hb
  | zero => rfl

theorem fqInitTrace_build {F : Type} (specs : List (String × FqInitFactor))
    (hfree : ∀ ne ∈ specs, ofString ne.1 ≠ ofString "a" ∧ ofString ne.1 ≠ ofString "b")
    (s : PanSemStateFiniteExact 64 F) (A B : Limbs256)
    (ha : s.locals.lookup (ofString "a") = some A.toValue)
    (hb : s.locals.lookup (ofString "b") = some B.toValue) :
    MontInitTrace s (fqInitExpressions specs) (montSetWords s (fqInitAssignments A B specs)) := by
  induction specs generalizing s with
  | nil => exact .nil s
  | cons ne rest ih =>
    obtain ⟨name, factor⟩ := ne
    have hn := hfree (name,factor) List.mem_cons_self
    have hrest : ∀ ne ∈ rest, ofString ne.1 ≠ ofString "a" ∧ ofString ne.1 ≠ ofString "b" :=
      fun ne hne => hfree ne (List.mem_cons_of_mem _ hne)
    have ha' : (setVarHOLFinite (ofString name) (.val (.word (fqInitValue A B factor))) s).locals.lookup
        (ofString "a") = some A.toValue := by
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn.1] using ha
    have hb' : (setVarHOLFinite (ofString name) (.val (.word (fqInitValue A B factor))) s).locals.lookup
        (ofString "b") = some B.toValue := by
      simpa [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, hn.2] using hb
    apply MontInitTrace.cons (fqInitValue A B factor) (fqInitFactor_eval s A B ha hb factor)
    apply ih <;> assumption

def fqInitSpecs : List (String × FqInitFactor) :=
  [("a0", .a 0),
   ("a1", .a 1),
   ("a2", .a 2),
   ("a3", .a 3),
   ("a4", .a 4),
   ("a5", .a 5),
   ("a6", .a 6),
   ("a7", .a 7),
   ("b0", .b 0),
   ("b1", .b 1),
   ("b2", .b 2),
   ("b3", .b 3),
   ("b4", .b 4),
   ("b5", .b 5),
   ("b6", .b 6),
   ("b7", .b 7),
   ("pr", .zero),
   ("L", .zero),
   ("H", .zero),
   ("c", .zero),
   ("col", .zero),
   ("col2", .zero),
   ("dg", .zero),
   ("m0", .zero),
   ("m1", .zero),
   ("m2", .zero),
   ("m3", .zero),
   ("m4", .zero),
   ("m5", .zero),
   ("m6", .zero),
   ("m7", .zero),
   ("u0", .zero),
   ("u1", .zero),
   ("u2", .zero),
   ("u3", .zero),
   ("u4", .zero),
   ("u5", .zero),
   ("u6", .zero)]

theorem fqInitializers_source_eq : fqMulInitializers = fqInitExpressions fqInitSpecs := rfl

theorem fqInitSpecs_names :
    ∀ ne ∈ fqInitSpecs, ofString ne.1 ≠ ofString "a" ∧ ofString ne.1 ≠ ofString "b" := by
  intro ne hne
  simp only [fqInitSpecs, List.mem_cons, List.not_mem_nil, or_false] at hne
  rcases hne with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals decide

theorem fqInitAssignments_nodup (A B : Limbs256) :
    ((fqInitAssignments A B fqInitSpecs).map (fun ne => ofString ne.1)).Nodup := by
  change ([ofString "a0", ofString "a1", ofString "a2", ofString "a3", ofString "a4", ofString "a5", ofString "a6", ofString "a7", ofString "b0", ofString "b1", ofString "b2", ofString "b3", ofString "b4", ofString "b5", ofString "b6", ofString "b7", ofString "pr", ofString "L", ofString "H", ofString "c", ofString "col", ofString "col2", ofString "dg", ofString "m0", ofString "m1", ofString "m2", ofString "m3", ofString "m4", ofString "m5", ofString "m6", ofString "m7", ofString "u0", ofString "u1", ofString "u2", ofString "u3", ofString "u4", ofString "u5", ofString "u6"]).Nodup
  decide

theorem fqInitializers_trace {F : Type} (s : PanSemStateFiniteExact 64 F) (A B : Limbs256)
    (ha : s.locals.lookup (ofString "a") = some A.toValue)
    (hb : s.locals.lookup (ofString "b") = some B.toValue) :
    MontInitTrace s fqMulInitializers (montSetWords s (fqInitAssignments A B fqInitSpecs)) := by
  rw [fqInitializers_source_eq]
  exact fqInitTrace_build fqInitSpecs fqInitSpecs_names s A B ha hb

end InitECandidate.Solver.Wave8GuestInv.Arith
