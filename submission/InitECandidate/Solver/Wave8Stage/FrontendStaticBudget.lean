import InitECandidate.Solver.Wave8Stage.FrontendCostTransfer

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.FrontendStaticBudget
open Classical Flapjack Flapjack.Basis.Pure.MlString
open CrepSourceCostBound FrontendCostTransfer

/-- A deterministic structural frontend potential, over the actual compiled
association list. Unlike finite-support choice, it can be reduced directly
when instantiating a concrete AST budget. Shadowed duplicate entries are
conservatively included. -/
def listBudget {width : Nat} [NeZero width]
    (code : List (MlString × List Nat × CrepProgHOL width)) : Nat :=
  (code.map fun entry => programCost (crepSimpProgHOL entry.2.2)).foldr max 3

private theorem fold_base (values : List Nat) : 3 ≤ values.foldr max 3 := by
  induction values with
  | nil => exact Nat.le_refl _
  | cons value values ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

private theorem fold_member (values : List Nat) (value : Nat) (member : value ∈ values) :
    value ≤ values.foldr max 3 := by
  induction values with
  | nil => cases member
  | cons head values ih =>
    rcases List.mem_cons.mp member with rfl | tail
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih tail) (Nat.le_max_right _ _)

private theorem lookup_member {width : Nat} [NeZero width]
    (entries : List (MlString × List Nat × CrepProgHOL width))
    (name : MlString) (value : List Nat × CrepProgHOL width)
    (lookup : (alistToFmapCodeExact entries).lookup name = some value) :
    (name,value) ∈ entries := by
  have raw : FLOOKUP (FUPDATE_LIST (FEMPTY : FiniteMap MlString (List Nat × CrepProgHOL width))
      entries.reverse) name = some value := by
    simp only [alistToFmapCodeExact,HolFiniteMapExact.lookup_updateList] at lookup
    exact lookup
  rcases flookupFupdateList_mem_or_base
    (FEMPTY : FiniteMap MlString (List Nat × CrepProgHOL width)) entries.reverse name value raw
    with ⟨entry,member,keyEq,valueEq⟩ | base
  · have equal : (name,value) = entry := by
      rcases entry with ⟨key,body⟩
      exact Prod.ext keyEq.symm valueEq.symm
    rw [equal]
    exact List.mem_reverse.mp member
  · simp [FLOOKUP_empty] at base

theorem listBudget_bounds {width : Nat} [NeZero width]
    (code : List (MlString × List Nat × CrepProgHOL width)) :
    codeCostBound (simplifiedCode (alistToFmapCodeExact code)) (listBudget code) := by
  intro name params body lookup
  cases raw : (alistToFmapCodeExact code).lookup name with
  | none => simp [simplifiedCode,HolFiniteMapExact.lookup_map2,raw] at lookup
  | some value =>
    rcases value with ⟨originalParams,originalBody⟩
    have member := lookup_member code name (originalParams,originalBody) raw
    simp only [simplifiedCode,HolFiniteMapExact.lookup_map2,raw,Option.map_some,
      Option.some.injEq,Prod.mk.injEq] at lookup
    obtain ⟨rfl,rfl⟩ := lookup
    exact fold_member _ _ (List.mem_map.mpr ⟨(name,originalParams,originalBody),member,rfl⟩)

theorem crepBudget_le_listBudget {width : Nat} [NeZero width]
    (code : List (MlString × List Nat × CrepProgHOL width)) :
    crepBudget code ≤ listBudget code :=
  CrepCodeBudget.codeBound_le _ _ (fold_base _) (listBudget_bounds code)

noncomputable def staticFrontBudget {width : Nat} [NeZero width]
    (code : List (Pancake.PanLang.DeclHOL width)) (start : MlString) : Nat :=
  listBudget (compileProgDeclsHOLW (compileTopExactHOL
    (Pancake.PanStructs.CompileShapeExact.compileTopExact (panSimpDeclsHOL code)) start))

theorem frontBudget_le_staticFrontBudget {width : Nat} [NeZero width]
    (code : List (Pancake.PanLang.DeclHOL width)) (start : MlString) :
    frontBudget code start ≤ staticFrontBudget code start :=
  crepBudget_le_listBudget _

#print axioms listBudget_bounds
#print axioms crepBudget_le_listBudget
#print axioms frontBudget_le_staticFrontBudget

end InitECandidate.Solver.Wave8Stage.FrontendStaticBudget
