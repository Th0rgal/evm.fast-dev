import InitECandidate.Solver.Wave8Stage.CertifiedMapReduction
import Flapjack.Pancake.PanToWord

/-! Keep shared metadata maps unevaluated until lookup, and expose metadata list
operations before their program-list arguments. Unused body terms stay unevaluated.
All replacements are justified by definitional equality in kernel-checked proofs. -/
open Lean Meta Flapjack

private def exposeMetadata : Sym.Simp.Simproc := fun expression => do
  let result ← withTransparency .all (whnf expression)
  let result := wave8BetaListHead result
  if result == expression then return .rfl
  return .step result (← mkEqRefl expression)

/- Preserve the kernel's literal-string reduction instead of exposing the
UTF-8 iterator one character at a time through the lazy List.map simproc. -/
cbv_simproc ↓ wave8LiteralString (Flapjack.Basis.Pure.MlString.ofString _) := fun expression => do
  let string ← withTransparency .all (whnf expression.appArg!)
  let some value := Sym.getStringValue? string | return .rfl
  let bytes := value.toList.map fun character =>
    mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 8) (mkNatLit character.toNat)
  let list ← mkListLit (mkApp (mkConst ``BitVec) (mkNatLit 8)) bytes
  let result ← Sym.shareCommon <| mkApp (mkConst ``Flapjack.Basis.Pure.MlString.MlString.implode) list
  return .step result (← mkEqRefl expression)

cbv_simproc ↓ wave8FunctionMap (makeFuncsExactHOL _) := fun _ => return .rfl (done := true)
cbv_simproc ↓ wave8ExceptionMap (getEidsFromDeclsHOL _) := fun _ => return .rfl (done := true)
cbv_simproc ↓ wave8LoopMap (crepToLoopMakeFuncsExactExecutable _) := fun _ => return .rfl (done := true)
/- Reduce lengths one list constructor at a time. In particular, use the
range-length theorem before forcing the range's bound: that bound can contain
well-founded shape compilation which CBV must handle by equation lemmas. -/
cbv_simproc ↓ wave8Length (List.length _) := fun expression => do
  let list := expression.appArg!
  if let some range ← withTransparency .all (whnfUntil list ``List.range) then
    let size := range.appArg!
    return .step size (← mkAppOptM ``List.length_range #[some size])
  let list ← withTransparency .all (whnf list)
  if list.isAppOfArity ``List.cons 3 then
    let args := list.getAppArgs
    let proof ← mkAppOptM ``List.length_cons #[some args[0]!, some args[1]!, some args[2]!]
    let some (_, _, result) := (← inferType proof).eq? | return .rfl
    return .step result proof
  if list.isAppOfArity ``List.nil 1 then
    return .step (mkNatLit 0) (← mkEqRefl expression)
  return .rfl

cbv_simproc ↓ wave8FunctionEntries (makeFuncsEntriesHOL _) := exposeMetadata
cbv_simproc ↓ wave8ExceptionEntries (getEidsEntriesHOL _) := exposeMetadata
cbv_simproc ↓ wave8Functions (Flapjack.Pancake.PanLang.functionsHOL _) := exposeMetadata
cbv_simproc ↓ wave8Exceptions (Flapjack.Pancake.PanLang.exceptionsHOL _) := exposeMetadata
cbv_simproc ↓ wave8Zip (List.zip _ _) := exposeMetadata
cbv_simproc ↓ wave8AlistLookup (alistToFmap _ _) := exposeMetadata
cbv_simproc ↓ wave8FoldrApply (List.foldr (β := _ → _) _ _ _ _) := exposeMetadata
cbv_simproc ↓ wave8FoldlApply (List.foldl (α := _ → _) _ _ _ _) := exposeMetadata
cbv_simproc ↓ wave8UpdateListLookup (FUPDATE_LIST _ _ _) := exposeMetadata

cbv_simproc ↓ wave8ClosedLookup (HolFiniteMapExact.lookup _ _) := exposeMetadata
cbv_simproc ↓ wave8Filter (List.filter _ _) := exposeMetadata

/- Read structure metadata before traversing the declarations' program bodies. -/
cbv_simproc ↓ wave8StructNames (Flapjack.Pancake.PanStructs.CompileShapeExact.getNamesExact _ _) := exposeMetadata
