import InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrepLower

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrep
open Flapjack

/- Stage the shared inline support before capturing it in every body. In this
guest it is empty; its certificate avoids repeated traversal of the full code. -/
wave8_certified_reduce inlineEntries := ConcreteCompilerCrepLower.lowered.filter
  (fun triple => ConcreteCompilerCrepContext.inlineNames.contains triple.1)

def applyInline
    (entries : List (Flapjack.Pancake.PanLang.MlS × List Nat × CrepProgHOL 64))
    (code : List (Flapjack.Pancake.PanLang.MlS × List Nat × CrepProgHOL 64)) :=
  CrepInlineCanonical.compileInlProgHOLExactWithSupport
    (CrepInlineCanonical.alistToFmapHOLExact entries) (entries.map Prod.fst)
    (CrepInlineCanonical.supportKeys_alistToFmapHOLExact entries) code

wave8_list_spine inlined := applyInline inlineEntries ConcreteCompilerCrepLower.lowered

theorem inline_eq : CrepInlineCanonical.compileInlTopHOLExact
    ConcreteCompilerCrepContext.inlineNames ConcreteCompilerCrepLower.lowered = inlined :=
  (congrArg (fun entries => applyInline entries ConcreteCompilerCrepLower.lowered)
    inlineEntries_eq).trans inlined_eq

noncomputable def source := inlined

theorem source_eq : compileProgDeclsHOLW ConcreteCompilerGlobals.source = source := by
  exact CrepCompilerComposition.assemble ConcreteCompilerGlobals.source
    ConcreteCompilerCrepContext.functions ConcreteCompilerCrepContext.inlineNames
    ConcreteCompilerCrepContext.functionMap ConcreteCompilerCrepContext.exceptions
    ConcreteCompilerCrepLower.lowered source
    ConcreteCompilerCrepContext.functions_eq ConcreteCompilerCrepContext.inlineNames_eq
    ConcreteCompilerCrepContext.functionMap_eq ConcreteCompilerCrepContext.exceptions_eq
    ConcreteCompilerCrepLower.lowered_eq inline_eq

#print axioms source_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrep
