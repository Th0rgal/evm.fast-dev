import InitECandidate.Solver.Wave8Stage.CrepSourceCostBound

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CrepCodeBudget
open Classical Flapjack CrepSourceCostBound

/-- A finite source-code potential, including the entry-call allowance. -/
noncomputable def codeBound {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) : Nat :=
  ((Classical.choose code.finiteSupport).map fun name =>
    match code.lookup name with
    | none => 0
    | some (_, body) => programCost body).foldr max 3

private theorem fold_max_base (xs : List Nat) : 3 ≤ xs.foldr max 3 := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih => exact Nat.le_trans ih (Nat.le_max_right _ _)

private theorem fold_max_member (xs : List Nat) (n : Nat) (h : n ∈ xs) :
    n ≤ xs.foldr max 3 := by
  induction xs with
  | nil => cases h
  | cons x xs ih =>
    simp only [List.mem_cons] at h
    rcases h with rfl | h
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem codeBound_ge_three {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) :
    3 ≤ codeBound code := fold_max_base _

theorem codeBound_bounds {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width)) :
    codeCostBound code (codeBound code) := by
  intro name params body hlookup
  apply fold_max_member
  apply List.mem_map.mpr
  refine ⟨name, Classical.choose_spec code.finiteSupport name (by rw [hlookup]; simp), ?_⟩
  simp only [hlookup]

/-- Any certified code bound above the entry allowance also bounds the
choice-based support enumeration. Extra unused support keys contribute zero. -/
theorem codeBound_le {width : Nat} [NeZero width]
    (code : HolFiniteMapExact Basis.Pure.MlString.MlString (List Nat × CrepProgHOL width))
    (bound : Nat) (entry : 3 ≤ bound) (bodies : codeCostBound code bound) :
    codeBound code ≤ bound := by
  suffices allKeys : ∀ keys : List Basis.Pure.MlString.MlString,
      ((keys.map fun name => match code.lookup name with
        | none => 0
        | some (_,body) => programCost body).foldr max 3) ≤ bound from
    allKeys _
  intro keys
  induction keys with
  | nil => exact entry
  | cons name keys ih =>
    simp only [List.map_cons,List.foldr_cons]
    cases lookup : code.lookup name with
    | none => simpa using ih
    | some value =>
      rcases value with ⟨params,body⟩
      have := bodies name params body lookup
      dsimp only
      omega

end InitECandidate.Solver.Wave8Stage.CrepCodeBudget
