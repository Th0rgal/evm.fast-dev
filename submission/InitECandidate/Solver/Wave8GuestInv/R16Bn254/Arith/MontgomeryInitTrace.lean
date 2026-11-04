import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqMulSource

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

def montDeclareWords (initializers : List (String × ExpHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 :=
  initializers.foldr (fun ne body => .dec (ofString ne.1) .one ne.2 body) tail

/-- Exact initializer evaluations, recording the state inside all declaration
scopes. Return values can be transferred through the later scope restoration. -/
inductive MontInitTrace {F : Type} : PanSemStateFiniteExact 64 F →
    List (String × ExpHOL 64) → PanSemStateFiniteExact 64 F → Prop where
  | nil (s) : MontInitTrace s [] s
  | cons {s final} {name : String} {expr : ExpHOL 64} {rest}
      (word : BitVec 64) (he : arithEval s expr = some (.val (.word word)))
      (tail : MontInitTrace (setVarHOLFinite (ofString name) (.val (.word word)) s) rest final) :
      MontInitTrace s ((name,expr) :: rest) final

theorem montInitTrace_code {F : Type} {s final : PanSemStateFiniteExact 64 F}
    {initializers : List (String × ExpHOL 64)} (h : MontInitTrace s initializers final) :
    final.code = s.code := by
  induction h with
  | nil => rfl
  | cons word he tail ih => exact ih

theorem montInitTrace_returned {F : Type} {s final post : PanSemStateFiniteExact 64 F}
    {initializers : List (String × ExpHOL 64)} (h : MontInitTrace s initializers final)
    (tail : ProgHOL 64) (ret : ValueHOL 64)
    (he : evaluateHOLFiniteState s (montDeclareWords initializers tail) =
      (some (.returned ret), post)) :
    ∃ inner : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState final tail = (some (.returned ret), inner) := by
  induction h generalizing post with
  | nil => exact ⟨post, he⟩
  | @cons s final name expr rest word hinit trace ih =>
    change evaluateHOLFiniteState s
      (.dec (ofString name) .one expr (montDeclareWords rest tail)) = _ at he
    obtain ⟨value, hvalue, hshape, inner, hbody⟩ := arith_dec_returned he
    change arithEval s expr = some value at hvalue
    have hv : value = .val (.word word) := Option.some.inj (hvalue.symm.trans hinit)
    subst value
    exact ih hbody

theorem montInitTrace_lookup_other {F : Type} {s final : PanSemStateFiniteExact 64 F}
    {initializers : List (String × ExpHOL 64)} (h : MontInitTrace s initializers final)
    (key : MlS) (hfree : ∀ ne ∈ initializers, key ≠ ofString ne.1) :
    final.locals.lookup key = s.locals.lookup key := by
  induction h with
  | nil => rfl
  | @cons s final name expr rest word hinit trace ih =>
    have hn : key ≠ ofString name := hfree (name,expr) (by simp)
    have hr : ∀ ne ∈ rest, key ≠ ofString ne.1 :=
      fun ne hne => hfree ne (List.mem_cons_of_mem _ hne)
    exact (ih hr).trans (by
      simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hn])

end InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith
