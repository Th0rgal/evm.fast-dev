import InitECandidate.Solver.CrepKernelComputation
import InitECandidate.Solver.Wave8Stage.ConcreteCompilerCrep
import InitECandidate.Solver.Wave8Stage.FrontendStaticBudget

/-!
# Structural Crep Cost Upper Bound Infrastructure

Proves that `crepSimpProgHOL` is cost-non-increasing (`programCost (crepSimpProgHOL p) ≤ programCost p`)
and provides structural `progCostStruct` so `FrontendStaticBudget.listBudget ConcreteCompilerCrep.source`
can be bounded by chunked `kernel_rfl` without reducing well-founded `crepSimpProgHOL` or `sizeOf`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 2000000

namespace InitECandidate.Solver.Wave8Stage.CrepListBudgetSupport

open InitECandidate.Solver.Wave8Stage
open Flapjack Flapjack.CrepInlineCanonical

theorem inlineProg_emptyLookup {width : Nat} [NeZero width]
    (fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (keys : List CrepInlineMapHOLName)
    (support : ∀ key, fs.lookup key ≠ none → key ∈ keys)
    (emptyLookup : ∀ key, fs.lookup key = none) (p : CrepProgHOL width) :
    inlineProgHOLCoreExact fs keys support p = p := by
  cases p with
  | dec name value body =>
      rw [inlineProgHOLCoreExact_dec, inlineProg_emptyLookup fs keys support emptyLookup body]
  | seq a b =>
      rw [inlineProgHOLCoreExact_seq, inlineProg_emptyLookup fs keys support emptyLookup a,
        inlineProg_emptyLookup fs keys support emptyLookup b]
  | ite c a b =>
      rw [inlineProgHOLCoreExact_ite, inlineProg_emptyLookup fs keys support emptyLookup a,
        inlineProg_emptyLookup fs keys support emptyLookup b]
  | «while» c body =>
      rw [inlineProgHOLCoreExact_while, inlineProg_emptyLookup fs keys support emptyLookup body]
  | call ret name arguments =>
      cases ret with
      | none => rw [inlineProgHOLCoreExact_call_none, emptyLookup]
      | some ret =>
          rcases ret with ⟨returns, handler⟩
          cases handler with
          | none =>
              rw [inlineProgHOLCoreExact_call_returns]
              split
              · rfl
              · rw [emptyLookup]
          | some handler =>
              rcases handler with ⟨exception, body⟩
              rw [inlineProgHOLCoreExact_call_handler,
                inlineProg_emptyLookup fs keys support emptyLookup body]
  | _ => simp only [inlineProgHOLCoreExact]
termination_by sizeOf p

theorem compileInlProg_emptyLookup {width : Nat} [NeZero width]
    (fs : HolFiniteMapExact CrepInlineMapHOLName (List Nat × CrepProgHOL width))
    (keys : List CrepInlineMapHOLName)
    (support : ∀ key, fs.lookup key ≠ none → key ∈ keys)
    (emptyLookup : ∀ key, fs.lookup key = none)
    (prog : List (CrepInlineMapHOLName × List Nat × CrepProgHOL width)) :
    compileInlProgHOLExactWithSupport fs keys support prog = prog := by
  unfold compileInlProgHOLExactWithSupport
  have identity : ∀ triple : CrepInlineMapHOLName × List Nat × CrepProgHOL width,
      inlineProgHOLCoreExact (fs.erase triple.1)
        (keys.filter (fun key => key != triple.1))
        (HolFiniteMapExact.erase_support fs keys support triple.1) triple.2.2 = triple.2.2 := by
    intro triple
    have emptyErase : ∀ key, (fs.erase triple.1).lookup key = none := by
      intro key
      simp [HolFiniteMapExact.lookup_erase, FDOMSUB, emptyLookup]
    exact inlineProg_emptyLookup _ _ _ emptyErase _
  simp only [identity]
  exact List.map_id prog

theorem crepMulConst_cost_le {width : Nat} [NeZero width] (e : CrepExpHOL width) (c : BitVec width) :
    CrepExpressionClock.expressionCost (crepMulConstHOL e c) ≤ CrepExpressionClock.expressionCost e := by
  unfold crepMulConstHOL
  split
  · simp [CrepExpressionClock.expressionCost]
  · split
    · exact Nat.le_refl _
    · cases crepDest2ExpHOL 0 c <;>
        simp [CrepExpressionClock.expressionCost, CrepExpressionClock.expressionsCost]

theorem expCost_simp {width : Nat} [NeZero width] :
    ∀ e : CrepExpHOL width,
      CrepExpressionClock.expressionCost (crepSimpExpHOL e) ≤ CrepExpressionClock.expressionCost e := by
  intro e
  induction e using (measure (sizeOf : CrepExpHOL width → Nat)).wf.induction with
  | h e ih =>
    change ∀ child, sizeOf child < sizeOf e →
      CrepExpressionClock.expressionCost (crepSimpExpHOL child) ≤ CrepExpressionClock.expressionCost child at ih
    have ihm : ∀ es : List (CrepExpHOL width), (∀ x ∈ es, sizeOf x < sizeOf e) →
        CrepExpressionClock.expressionsCost (es.map crepSimpExpHOL) ≤ CrepExpressionClock.expressionsCost es := by
      intro es hes
      induction es with
      | nil => simp [CrepExpressionClock.expressionsCost]
      | cons x xs ihxs =>
        simp only [List.map_cons, CrepExpressionClock.expressionsCost]
        exact Nat.add_le_add (ih x (hes x List.mem_cons_self))
          (ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy)))
    cases e with
    | crepOp op es =>
      have hlist := ihm es (by intros; sizeOf_list_dec)
      rw [crepSimpExpHOL.eq_def]
      dsimp only
      cases op
      cases hmap : es.map crepSimpExpHOL with
      | nil =>
        simp [CrepExpressionClock.expressionCost, CrepExpressionClock.expressionsCost]
      | cons a rest =>
        cases rest with
        | nil =>
          rw [hmap] at hlist
          simpa [CrepExpressionClock.expressionCost] using hlist
        | cons b rest2 =>
          cases rest2 with
          | nil =>
            rw [hmap] at hlist
            simp only [CrepExpressionClock.expressionsCost] at hlist
            cases ha : crepDestConstHOL a <;> cases hb : crepDestConstHOL b <;> simp only [ha, hb]
            · simpa [CrepExpressionClock.expressionCost, CrepExpressionClock.expressionsCost] using hlist
            · rename_i cb
              have hmul := crepMulConst_cost_le a cb
              simp only [CrepExpressionClock.expressionCost]
              omega
            · rename_i ca
              have hmul := crepMulConst_cost_le b ca
              simp only [CrepExpressionClock.expressionCost]
              omega
            · simp [CrepExpressionClock.expressionCost]
          | cons _ _ =>
            rw [hmap] at hlist
            simpa [CrepExpressionClock.expressionCost] using hlist
    | load a | load32 a | loadByte a =>
      simpa [crepSimpExpHOL, CrepExpressionClock.expressionCost] using ih a (by decreasing_trivial)
    | op op es =>
      simpa [crepSimpExpHOL, CrepExpressionClock.expressionCost] using ihm es (by intros; sizeOf_list_dec)
    | cmp op l r =>
      simp only [crepSimpExpHOL, CrepExpressionClock.expressionCost]
      have hl := ih l (by decreasing_trivial)
      have hr := ih r (by decreasing_trivial)
      omega
    | shift op l r =>
      simp only [crepSimpExpHOL, CrepExpressionClock.expressionCost]
      have hl := ih l (by decreasing_trivial)
      have hr := ih r (by decreasing_trivial)
      omega
    | const _ | var _ | loadGlob _ | baseAddr | topAddr =>
      simp [crepSimpExpHOL]

theorem expsCost_simp {width : Nat} [NeZero width] (es : List (CrepExpHOL width)) :
    CrepExpressionClock.expressionsCost (es.map crepSimpExpHOL) ≤ CrepExpressionClock.expressionsCost es := by
  induction es with
  | nil => simp [CrepExpressionClock.expressionsCost]
  | cons e es ih =>
    simp only [List.map_cons, CrepExpressionClock.expressionsCost]
    exact Nat.add_le_add (expCost_simp e) ih

theorem progCost_simp {width : Nat} [NeZero width] :
    ∀ p : CrepProgHOL width, CrepSourceCostBound.programCost (crepSimpProgHOL p) ≤ CrepSourceCostBound.programCost p := by
  intro p
  induction p using (measure (sizeOf : CrepProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p →
      CrepSourceCostBound.programCost (crepSimpProgHOL q) ≤ CrepSourceCostBound.programCost q at ih
    cases p with
    | dec n v b =>
      simp only [crepSimpProgHOL, CrepSourceCostBound.programCost]
      exact Nat.add_le_add (expCost_simp v) (ih b (by decreasing_trivial))
    | assign n v | storeGlob _ v | shMem _ _ v =>
      simpa [crepSimpProgHOL, CrepSourceCostBound.programCost] using expCost_simp v
    | store a v | store32 a v | storeByte a v =>
      simp only [crepSimpProgHOL, CrepSourceCostBound.programCost]
      exact Nat.add_le_add (expCost_simp a) (expCost_simp v)
    | seq a b =>
      simp only [crepSimpProgHOL, CrepSourceCostBound.programCost]
      exact Nat.add_le_add (ih a (by decreasing_trivial)) (ih b (by decreasing_trivial))
    | ite c a b =>
      simp only [crepSimpProgHOL, CrepSourceCostBound.programCost]
      have hc := expCost_simp c
      have ha := ih a (by decreasing_trivial)
      have hb := ih b (by decreasing_trivial)
      omega
    | «while» c b =>
      simp only [crepSimpProgHOL, CrepSourceCostBound.programCost]
      have hc := expCost_simp c
      have hb := ih b (by decreasing_trivial)
      omega
    | call ret name args =>
      have hargs := expsCost_simp args
      cases ret with
      | none =>
        simp only [crepSimpProgHOL, CrepSourceCostBound.programCost_call]
        omega
      | some r =>
        rcases r with ⟨rets, hdl⟩
        cases hdl with
        | none =>
          simp only [crepSimpProgHOL, CrepSourceCostBound.programCost_call]
          omega
        | some hb =>
          rcases hb with ⟨tag, body⟩
          simp only [crepSimpProgHOL, CrepSourceCostBound.programCost_call]
          have hb' := ih body (by simp_wf; omega)
          omega
    | «return» vs =>
      simpa [crepSimpProgHOL, CrepSourceCostBound.programCost] using expsCost_simp vs
    | skip | primitive _ _ _ | «break» _ | «continue» _ | extCall _ _ _ _ _ | raise _ | tick =>
      simp [crepSimpProgHOL, CrepSourceCostBound.programCost]

mutual
  def expCostStruct {width : Nat} [NeZero width] : (e : CrepExpHOL width) → Nat
    | .const _ => 0
    | .var _ => 0
    | .loadGlob _ => 0
    | .baseAddr => 0
    | .topAddr => 0
    | .load e => expCostStruct e
    | .load32 e => expCostStruct e
    | .loadByte e => expCostStruct e
    | .op _ es => expsCostStruct es
    | .crepOp _ es => expsCostStruct es
    | .cmp _ a b => expCostStruct a + expCostStruct b + 1
    | .shift _ a b => expCostStruct a + expCostStruct b
  termination_by structural e => e

  def expsCostStruct {width : Nat} [NeZero width] : (es : List (CrepExpHOL width)) → Nat
    | [] => 0
    | e :: es => expCostStruct e + expsCostStruct es
  termination_by structural es => es
end

theorem expCostStruct_eq {width : Nat} [NeZero width] :
    ∀ e : CrepExpHOL width, CrepExpressionClock.expressionCost e = expCostStruct e := by
  intro e
  induction e using (measure (sizeOf : CrepExpHOL width → Nat)).wf.induction with
  | h e ih =>
    change ∀ child, sizeOf child < sizeOf e → CrepExpressionClock.expressionCost child = expCostStruct child at ih
    have ihm : ∀ es : List (CrepExpHOL width), (∀ x ∈ es, sizeOf x < sizeOf e) →
        CrepExpressionClock.expressionsCost es = expsCostStruct es := by
      intro es hes
      induction es with
      | nil => rfl
      | cons x xs ihxs =>
        simp only [CrepExpressionClock.expressionsCost, expsCostStruct,
          ih x (hes x List.mem_cons_self),
          ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy))]
    cases e <;> simp only [CrepExpressionClock.expressionCost, expCostStruct]
    · exact ih _ (by decreasing_trivial)
    · exact ih _ (by decreasing_trivial)
    · exact ih _ (by decreasing_trivial)
    · exact ihm _ (by intros; sizeOf_list_dec)
    · exact ihm _ (by intros; sizeOf_list_dec)
    · rw [ih _ (by decreasing_trivial), ih _ (by decreasing_trivial)]
    · rw [ih _ (by decreasing_trivial), ih _ (by decreasing_trivial)]

theorem expsCostStruct_eq {width : Nat} [NeZero width] (es : List (CrepExpHOL width)) :
    CrepExpressionClock.expressionsCost es = expsCostStruct es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp only [CrepExpressionClock.expressionsCost, expsCostStruct, expCostStruct_eq, ih]

def progCostStruct {width : Nat} [NeZero width] : (p : CrepProgHOL width) → Nat
  | .skip => 0
  | .primitive _ _ _ => 0
  | .break _ => 0
  | .continue _ => 0
  | .extCall _ _ _ _ _ => 0
  | .raise _ => 0
  | .tick => 0
  | .assign _ e => expCostStruct e
  | .storeGlob _ e => expCostStruct e
  | .shMem _ _ e => expCostStruct e
  | .store a b => expCostStruct a + expCostStruct b
  | .store32 a b => expCostStruct a + expCostStruct b
  | .storeByte a b => expCostStruct a + expCostStruct b
  | .return es => expsCostStruct es
  | .dec _ e body => expCostStruct e + progCostStruct body
  | .seq first second => progCostStruct first + progCostStruct second
  | .ite e first second => expCostStruct e + 1 + progCostStruct first + progCostStruct second
  | .while e body => expCostStruct e + 2 + progCostStruct body
  | .call none _ args => expsCostStruct args + 3
  | .call (some (_, none)) _ args => expsCostStruct args + 3
  | .call (some (_, some (_, handler))) _ args => expsCostStruct args + 3 + progCostStruct handler
termination_by structural p => p

theorem progCostStruct_eq {width : Nat} [NeZero width] :
    ∀ p : CrepProgHOL width, CrepSourceCostBound.programCost p = progCostStruct p := by
  intro p
  induction p using (measure (sizeOf : CrepProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p → CrepSourceCostBound.programCost q = progCostStruct q at ih
    cases p with
    | assign _ e | storeGlob _ e | shMem _ _ e =>
      simp only [CrepSourceCostBound.programCost, progCostStruct, expCostStruct_eq]
    | store a b | store32 a b | storeByte a b =>
      simp only [CrepSourceCostBound.programCost, progCostStruct, expCostStruct_eq]
    | «return» es =>
      simp only [CrepSourceCostBound.programCost, progCostStruct, expsCostStruct_eq]
    | dec _ e body =>
      simp only [CrepSourceCostBound.programCost, progCostStruct, expCostStruct_eq, ih body (by decreasing_trivial)]
    | seq a b =>
      simp only [CrepSourceCostBound.programCost, progCostStruct, ih a (by decreasing_trivial), ih b (by decreasing_trivial)]
    | ite e a b =>
      simp only [CrepSourceCostBound.programCost, progCostStruct, expCostStruct_eq, ih a (by decreasing_trivial), ih b (by decreasing_trivial)]
    | «while» e b =>
      simp only [CrepSourceCostBound.programCost, progCostStruct, expCostStruct_eq, ih b (by decreasing_trivial)]
    | call ret n args =>
      cases ret with
      | none => simp only [CrepSourceCostBound.programCost_call, progCostStruct, expsCostStruct_eq, Nat.add_zero]
      | some r =>
        rcases r with ⟨rets, hdl⟩
        cases hdl with
        | none => simp only [CrepSourceCostBound.programCost_call, progCostStruct, expsCostStruct_eq, Nat.add_zero]
        | some hb =>
          rcases hb with ⟨tag, handler⟩
          simp only [CrepSourceCostBound.programCost_call, progCostStruct, expsCostStruct_eq, ih handler (by simp_wf; omega)]
    | skip | primitive _ _ _ | «break» _ | «continue» _ | extCall _ _ _ _ _ | raise _ | tick =>
      simp only [CrepSourceCostBound.programCost, progCostStruct]

noncomputable def fnRawCost
    (fn : Flapjack.Pancake.PanLang.MlS × List (Flapjack.Pancake.PanLang.MlS × Flapjack.Pancake.PanLang.ShapeHOL) ×
      Flapjack.Pancake.PanLang.ProgHOL 64 × Flapjack.Pancake.PanLang.ShapeHOL) : Nat :=
  progCostStruct (InitECandidate.Solver.CrepKernelComputation.compFuncExactHOLW
    ConcreteCompilerCrepContext.functionMap ConcreteCompilerCrepContext.exceptions fn.2.1 fn.2.2.1)

theorem foldr_max_mono : ∀ (xs ys : List Nat) (init : Nat),
    List.Forall₂ (· ≤ ·) xs ys → xs.foldr max init ≤ ys.foldr max init
  | [], [], _, _ => Nat.le_refl _
  | _ :: xs, _ :: ys, init, .cons hxy hrest =>
    Nat.max_le.mpr ⟨Nat.le_trans hxy (Nat.le_max_left _ _),
      Nat.le_trans (foldr_max_mono xs ys init hrest) (Nat.le_max_right _ _)⟩

theorem foldr_max_append (xs ys : List Nat) (init : Nat) :
    (xs ++ ys).foldr max init = xs.foldr max (ys.foldr max init) :=
  List.foldr_append

theorem foldr_max_le_of_parts (xs ys : List Nat) (bound : Nat)
    (hx : xs.foldr max 3 ≤ bound) (hy : ys.foldr max 3 ≤ bound) :
    (xs ++ ys).foldr max 3 ≤ bound := by
  induction xs with
  | nil => simpa using hy
  | cons x xs ih =>
    simp only [List.cons_append, List.foldr_cons] at hx ⊢
    exact Nat.max_le.mpr ⟨Nat.le_trans (Nat.le_max_left _ _) hx,
      ih (Nat.le_trans (Nat.le_max_right _ _) hx)⟩

theorem listBudget_le_raw :
    FrontendStaticBudget.listBudget ConcreteCompilerCrep.source ≤
      (ConcreteCompilerCrepContext.functions.map fnRawCost).foldr max 3 := by
  have hinl : ConcreteCompilerCrep.source = ConcreteCompilerCrepLower.lowered := by
    unfold ConcreteCompilerCrep.source
    rw [← ConcreteCompilerCrep.inlined_eq]
    have hempty : ConcreteCompilerCrep.inlineEntries = [] := rfl
    rw [hempty]
    exact compileInlProg_emptyLookup
      (CrepInlineCanonical.alistToFmapHOLExact []) []
      (CrepInlineCanonical.supportKeys_alistToFmapHOLExact [])
      (fun _ => rfl)
      ConcreteCompilerCrepLower.lowered
  rw [hinl, ← ConcreteCompilerCrepLower.lowered_eq]
  unfold CrepCompilerComposition.lower FrontendStaticBudget.listBudget
  rw [List.map_map]
  apply foldr_max_mono
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  intro fn _
  dsimp only [Function.comp_def, fnRawCost]
  rw [← InitECandidate.Solver.CrepKernelComputation.compFunc_function_eq, ← progCostStruct_eq]
  exact progCost_simp _

end InitECandidate.Solver.Wave8Stage.CrepListBudgetSupport
