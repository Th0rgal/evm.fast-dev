import InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobals
import InitECandidate.Solver.Wave8Stage.CertifiedListSpine

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrepContext
open InitE Flapjack Lean

local cbv_simproc ↓ freezeCodec (Flapjack.Pancake.PanLang.progToHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeSimp (panSimpCompileHOL _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeStruct (Flapjack.Pancake.PanStructs.CompileShapeExact.compileProgExact _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezePerm (fpermHOL _ _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeGlobals (compileProgExactHOL _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeCrep (compFuncExactHOLW _ _ _ _) := fun _ => return .rfl (done := true)
local cbv_simproc ↓ freezeInline (Flapjack.CrepInlineCanonical.inlineProgHOLCoreExact _ _ _ _) := fun _ => return .rfl (done := true)

wave8_list_spine functions := Flapjack.Pancake.PanLang.functionsHOL ConcreteCompilerGlobals.source

/-- A literal metadata association list, with the standard finite-support
proof. Program bodies never occur in this map. -/
def metadataMap {α β : Type} [BEq α] [LawfulBEq α]
    (entries : List (α × β)) : HolFiniteMapExact α β where
  lookup := alistToFmap entries
  finiteSupport := by
    refine ⟨entries.map Prod.fst, ?_⟩
    intro key hkey
    obtain ⟨value, hvalue⟩ := Option.ne_none_iff_exists'.mp hkey
    obtain ⟨entry, hentry, hkeyeq, -⟩ := flookupAlistToFmap_mem entries key value hvalue
    exact List.mem_map.mpr ⟨entry, hentry, hkeyeq⟩

wave8_certified_reduce functionEntries := makeFuncsEntriesHOL functions
noncomputable def functionMap := metadataMap functionEntries
theorem functionMap_eq : makeFuncsExactHOL functions = functionMap :=
  congrArg metadataMap functionEntries_eq

wave8_certified_reduce exceptionEntries := getEidsEntriesHOL ConcreteCompilerGlobals.source
noncomputable def exceptions := metadataMap exceptionEntries
theorem exceptions_eq : getEidsFromDeclsHOL ConcreteCompilerGlobals.source = exceptions :=
  congrArg metadataMap exceptionEntries_eq
wave8_list_spine inlineNames :=
  (Flapjack.Pancake.PanLang.functionsHOL
    (ConcreteCompilerGlobals.source.filter Flapjack.Pancake.PanLang.inlinableHOL)).map Prod.fst

#print axioms functions_eq
#print axioms functionMap_eq
#print axioms exceptions_eq
#print axioms inlineNames_eq
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrepContext
