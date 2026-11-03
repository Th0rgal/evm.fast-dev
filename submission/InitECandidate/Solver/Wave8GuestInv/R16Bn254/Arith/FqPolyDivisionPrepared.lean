import InitECandidate.Solver.Wave8GuestInv.Expressions
import InitECandidate.Solver.Wave8GuestInv.R16Bn254.Arith.FqPolyDivisionEntry

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
set_option linter.unreachableTactic false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
namespace InitECandidate.Solver.Wave8GuestInv.Arith
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.GuestCodeLookup
open InitECandidate.Solver.PanRunBounded

/-- The actual inverse prefix and inner loop pass a canonical smaller
remainder to the cofactor-update continuation. No inverse is assumed at entry. -/
theorem polyDivPreparedLoop_none {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (a b quotient : BitVec 64) (d1 : Nat) (B : Nat → Limbs256) (cont : ProgHOL 64)
    (ctx : PolyDivEntryContext a b quotient d1 B)
    (hc : state.code = originalRuntimeCode) (hi : PolyDivEntryInvariant a b quotient d1 B state)
    (hr : evaluateHOLFiniteState state (polyDivPrepare (.seq polyDivLoop cont)) = (none,post)) :
    ∃ (inverse : Limbs256) (resumed inner : PanSemStateFiniteExact 64 F),
      PolyDivContext a b quotient d1 B inverse ∧
      PolyDivInvariant a b quotient d1 B inverse resumed ∧
      (∃ degree : BitVec 64, resumed.locals.lookup (ofString "d0") = some (.val (.word degree)) ∧
        degree.toInt < (d1 : Int)) ∧
      resumed.code = state.code ∧
      (∀ x, PolynomialOutside a x → PolynomialOutside quotient x → resumed.memory x = state.memory x) ∧
      evaluateHOLFiniteState resumed cont = (none,inner) ∧ post.memory = inner.memory ∧
      ∀ name, name ≠ ofString "lead" → name ≠ ofString "linv" →
        post.locals.lookup name = inner.locals.lookup name := by
  obtain ⟨inverse,entry,inner,hctx,hentry,hcode,hmem,hseq,hfinalMem,hfinalLocals⟩ :=
    polyDivPrepare_none state post a b quotient d1 B (.seq polyDivLoop cont) ctx hc hi hr
  obtain ⟨resumed,hloop,hcont⟩ := arith_seq_none hseq
  obtain ⟨hinv,hexit,hrank,hframe⟩ :=
    polyDivLoop_none entry resumed a b quotient d1 B inverse hctx (hcode.trans hc) hentry hloop
  have hmeta := evaluateHOLFiniteState_metadata entry polyDivLoop
  rw [hloop] at hmeta
  refine ⟨inverse,resumed,inner,hctx,hinv,hexit,hmeta.1.trans hcode,?_,hcont,hfinalMem,hfinalLocals⟩
  intro x hxa hxq
  rw [hframe x hxa hxq,hmem]

end InitECandidate.Solver.Wave8GuestInv.Arith
