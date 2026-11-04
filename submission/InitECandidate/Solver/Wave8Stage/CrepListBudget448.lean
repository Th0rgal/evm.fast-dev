import InitECandidate.Proofs.FrontendCodecComputation
import InitECandidate.Proofs.GlobalsKernelComputation
import InitECandidate.Solver.Wave8Stage.CrepListBudgetSupport
import InitECandidate.Solver.Wave8Stage.R12_Stage1To2BoundArgon

/-!
# Analytical Frontend Crep Budget Bound (`listBudget ConcreteCompilerCrep.source ≤ 448`)

Proves `FrontendStaticBudget.listBudget ConcreteCompilerCrep.source ≤ 448` analytically via:
1. Syntactic PanLang cost (`panExpCost`, `panProgCost`) and structural invariants
   (`shapeFree`, `expFree`, `progFree`, `loadSafeExp`, `progNoGlobCall`) preserved across
   `mainFirstHOL`, `panSimpDeclsHOL`, `compileTopExact`, and `compileTopExactHOL`.
2. Exact PanToCrep cost upper bound (`programCost (compFuncExactHOLW ...) ≤ panProgCost body`).
3. Single fast structural `kernel_rfl` check on `Guest.Software.guestAst`.
-/

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000

namespace InitECandidate.Solver.Wave8Stage.CrepListBudget448

open InitE
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.Pancake.PanStructs.CompileShapeExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Solver.Wave8Stage
open InitECandidate.Solver.Wave8Stage.CrepExpressionClock
open InitECandidate.Solver.Wave8Stage.CrepSourceCostBound
open InitECandidate.Solver.Wave8Stage.FrontendCostTransfer
open InitECandidate.Solver.Wave8Stage.FrontendStaticBudget
open InitECandidate.Solver.Wave8Stage.CrepListBudgetSupport

/-! ## 1. PanLang Syntactic Cost and Structural Invariants (HOL Carrier) -/

mutual
  def panExpCost {width : Nat} [NeZero width] : (e : ExpHOL width) → Nat
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 0
    | .rstruct es | .op _ es | .panop _ es => panExpsCost es
    | .rfield _ e | .load _ e | .load32 e | .loadByte e | .nfield _ e => panExpCost e
    | .nstruct _ fs => panNamedExpsCost fs
    | .cmp _ a b => panExpCost a + panExpCost b + 1
    | .shift _ a b => panExpCost a + panExpCost b
  termination_by structural e => e

  def panExpsCost {width : Nat} [NeZero width] : (es : List (ExpHOL width)) → Nat
    | [] => 0
    | e :: es => panExpCost e + panExpsCost es
  termination_by structural es => es

  def panNamedExpsCost {width : Nat} [NeZero width] : (fs : List (MlS × ExpHOL width)) → Nat
    | [] => 0
    | (_, e) :: fs => panExpCost e + panNamedExpsCost fs
  termination_by structural fs => fs
end

def panProgCost {width : Nat} [NeZero width] : (p : ProgHOL width) → Nat
  | .skip | .break | .continue | .tick | .annot _ _ => 0
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => panExpCost e
  | .primitive _ _ es => panExpsCost es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => panExpCost a + panExpCost b
  | .dec _ _ e body => panExpCost e + panProgCost body
  | .decCall _ _ _ args body => panExpsCost args + 3 + panProgCost body
  | .seq a b => panProgCost a + panProgCost b
  | .ite c a b => panExpCost c + 1 + panProgCost a + panProgCost b
  | .while c body => panExpCost c + 2 + panProgCost body
  | .extCall _ e1 e2 e3 e4 => panExpCost e1 + panExpCost e2 + panExpCost e3 + panExpCost e4
  | .call none _ args => panExpsCost args + 3
  | .call (some (_, none)) _ args => panExpsCost args + 3
  | .call (some (_, some (_, _, body))) _ args => panExpsCost args + 3 + panProgCost body
termination_by structural p => p

mutual
  def shapeFree : ShapeHOL → Bool
    | .one => true
    | .comb shapes => shapesFree shapes
    | .named _ => false
  termination_by structural shape => shape

  def shapesFree : List ShapeHOL → Bool
    | [] => true
    | shape :: shapes => shapeFree shape && shapesFree shapes
  termination_by structural shapes => shapes
end

mutual
  def expFree {width : Nat} [NeZero width] : (e : ExpHOL width) → Bool
    | .nstruct _ _ | .nfield _ _ => false
    | .rstruct fields => expsFree fields
    | .rfield _ value => expFree value
    | .load shape address => shapeFree shape && expFree address
    | .loadByte address | .load32 address => expFree address
    | .op _ args | .panop _ args => expsFree args
    | .cmp _ left right | .shift _ left right => expFree left && expFree right
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
  termination_by structural e => e

  def expsFree {width : Nat} [NeZero width] : (es : List (ExpHOL width)) → Bool
    | [] => true
    | e :: es => expFree e && expsFree es
  termination_by structural es => es
end

def progFree {width : Nat} [NeZero width] : (p : ProgHOL width) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ value | .return value | .raise _ value | .shMemLoad _ _ _ value => expFree value
  | .primitive _ _ args => expsFree args
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => expFree a && expFree b
  | .dec _ shape value body => shapeFree shape && expFree value && progFree body
  | .decCall _ shape _ args body => shapeFree shape && expsFree args && progFree body
  | .seq first second => progFree first && progFree second
  | .ite condition first second => expFree condition && progFree first && progFree second
  | .while condition body => expFree condition && progFree body
  | .extCall _ c cl a al => expFree c && expFree cl && expFree a && expFree al
  | .call none _ args => expsFree args
  | .call (some (_, none)) _ args => expsFree args
  | .call (some (_, some (_, _, body))) _ args => expsFree args && progFree body
termination_by structural p => p

def declarationFree {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .function fn => (fn.params.all fun p => shapeFree p.2) && progFree fn.body && shapeFree fn.returnShape
  | .decl shape _ value => shapeFree shape && expFree value
  | .exnDecl _ shape => shapeFree shape
  | .name _ _ => false

mutual
  def loadSafeExp {width : Nat} [NeZero width] : (e : ExpHOL width) → Bool
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
    | .rstruct es | .op _ es | .panop _ es => loadSafeExps es
    | .rfield _ e | .load32 e | .loadByte e | .nfield _ e => loadSafeExp e
    | .load shape e => (decide (sizeOfShapeHOL shape ≤ 1) || decide (panExpCost e = 0)) && loadSafeExp e
    | .nstruct _ fs => loadSafeNamed fs
    | .cmp _ a b | .shift _ a b => loadSafeExp a && loadSafeExp b
  termination_by structural e => e

  def loadSafeExps {width : Nat} [NeZero width] : (es : List (ExpHOL width)) → Bool
    | [] => true
    | e :: es => loadSafeExp e && loadSafeExps es
  termination_by structural es => es

  def loadSafeNamed {width : Nat} [NeZero width] : (fs : List (MlS × ExpHOL width)) → Bool
    | [] => true
    | (_, e) :: fs => loadSafeExp e && loadSafeNamed fs
  termination_by structural fs => fs
end

def loadSafeProg {width : Nat} [NeZero width] : (p : ProgHOL width) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => loadSafeExp e
  | .primitive _ _ es => loadSafeExps es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => loadSafeExp a && loadSafeExp b
  | .dec _ _ e body => loadSafeExp e && loadSafeProg body
  | .decCall _ _ _ args body => loadSafeExps args && loadSafeProg body
  | .seq a b => loadSafeProg a && loadSafeProg b
  | .ite c a b => loadSafeExp c && loadSafeProg a && loadSafeProg b
  | .while c body => loadSafeExp c && loadSafeProg body
  | .extCall _ e1 e2 e3 e4 => loadSafeExp e1 && loadSafeExp e2 && loadSafeExp e3 && loadSafeExp e4
  | .call none _ args => loadSafeExps args
  | .call (some (_, none)) _ args => loadSafeExps args
  | .call (some (_, some (_, _, body))) _ args => loadSafeExps args && loadSafeProg body
termination_by structural p => p

def progNoGlobCall {width : Nat} [NeZero width] : (p : ProgHOL width) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ _ | .return _ | .raise _ _ | .primitive _ _ _ => true
  | .store _ _ | .store32 _ _ | .storeByte _ _ | .shMemStore _ _ _ | .extCall _ _ _ _ _ => true
  | .shMemLoad _ .local _ _ => true
  | .shMemLoad _ .global _ _ => false
  | .dec _ _ _ body | .decCall _ _ _ _ body | .while _ body => progNoGlobCall body
  | .seq a b | .ite _ a b => progNoGlobCall a && progNoGlobCall b
  | .call none _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call (some (none, some (_, _, body))) _ _ => progNoGlobCall body
  | .call (some (some (.local, _), some (_, _, body))) _ _ => progNoGlobCall body
  | .call (some (some (.global, _), some _)) _ _ => false
termination_by structural p => p

def declGood {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .function fn =>
      !fn.inline &&
      declarationFree (.function fn : DeclHOL width) &&
      loadSafeProg fn.body &&
      progNoGlobCall fn.body &&
      decide (panProgCost fn.body ≤ 448)
  | .decl shape _ value =>
      shapeFree shape && expFree value && loadSafeExp value && decide (panExpCost value = 0)
  | .exnDecl _ shape => shapeFree shape
  | .name _ _ => false

/-! ## 2. PanStructs Identity on Struct-Free Declarations -/

theorem shape_identity {α : Type} (context : List (MlS × List (α × ShapeHOL))) :
    (∀ shape : ShapeHOL, shapeFree shape = true → compileShapeExact context shape = shape) ∧
    (∀ shapes : List ShapeHOL, shapesFree shapes = true → compileShapesExact context shapes = shapes) := by
  have hs : ∀ shape : ShapeHOL, shapeFree shape = true → compileShapeExact context shape = shape := by
    intro shape
    induction shape using (measure (sizeOf : ShapeHOL → Nat)).wf.induction with
    | h s ih =>
      change ∀ c, sizeOf c < sizeOf s → shapeFree c = true → compileShapeExact context c = c at ih
      have ihm : ∀ ss : List ShapeHOL, (∀ x ∈ ss, sizeOf x < sizeOf s) →
          shapesFree ss = true → compileShapesExact context ss = ss := by
        intro ss hss hfree
        induction ss with
        | nil => simp [compileShapesExact]
        | cons x xs ihxs =>
          simp only [shapesFree, Bool.and_eq_true_iff] at hfree
          simp only [compileShapesExact, ih x (hss x List.mem_cons_self) hfree.1,
            ihxs (fun y hy => hss y (List.mem_cons_of_mem _ hy)) hfree.2]
      cases s with
      | one => intro _; simp [compileShapeExact]
      | named _ => intro h; simp [shapeFree] at h
      | comb ss =>
        intro h; simp only [shapeFree] at h
        simp only [compileShapeExact, ihm ss (by intro x hx; have := List.sizeOf_lt_of_mem hx; simp only [ShapeHOL.comb.sizeOf_spec]; omega) h]
  refine ⟨hs, ?_⟩
  intro shapes hfree
  induction shapes with
  | nil => simp [compileShapesExact]
  | cons s ss ih =>
    simp only [shapesFree, Bool.and_eq_true_iff] at hfree
    simp only [compileShapesExact, hs s hfree.1, ih hfree.2]

theorem exp_identity {width : Nat} [NeZero width] (context : ContextExact) :
    (∀ e : ExpHOL width, expFree e = true → compileExpExact context e = e) ∧
    (∀ es : List (ExpHOL width), expsFree es = true → compileExpsExact context es = es) := by
  have he : ∀ e : ExpHOL width, expFree e = true → compileExpExact context e = e := by
    intro e
    induction e using (measure (sizeOf : ExpHOL width → Nat)).wf.induction with
    | h e ih =>
      change ∀ y, sizeOf y < sizeOf e → expFree y = true → compileExpExact context y = y at ih
      have ihm : ∀ es : List (ExpHOL width), (∀ x ∈ es, sizeOf x < sizeOf e) →
          expsFree es = true → compileExpsExact context es = es := by
        intro es hes hfree
        induction es with
        | nil => simp [compileExpsExact]
        | cons x xs ihxs =>
          simp only [expsFree, Bool.and_eq_true_iff] at hfree
          simp only [compileExpsExact, ih x (hes x List.mem_cons_self) hfree.1,
            ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy)) hfree.2]
      cases e with
      | const _ | var _ _ | baseAddr | topAddr | bytesInWord =>
        intro _; simp [compileExpExact]
      | nstruct _ _ | nfield _ _ =>
        intro h; simp [expFree] at h
      | rstruct fs =>
        intro h; simp only [expFree] at h
        simp only [compileExpExact, ihm fs (by intros; sizeOf_list_dec) h]
      | rfield _ v | loadByte v | load32 v =>
        intro h; simp only [expFree] at h
        simp only [compileExpExact, ih v (by decreasing_trivial) h]
      | load sh addr =>
        intro h; simp only [expFree, Bool.and_eq_true_iff] at h
        simp only [compileExpExact, (shape_identity context.structs).1 sh h.1, ih addr (by decreasing_trivial) h.2]
      | op _ args | panop _ args =>
        intro h; simp only [expFree] at h
        simp only [compileExpExact, ihm args (by intros; sizeOf_list_dec) h]
      | cmp _ l r | shift _ l r =>
        intro h; simp only [expFree, Bool.and_eq_true_iff] at h
        simp only [compileExpExact, ih l (by decreasing_trivial) h.1, ih r (by decreasing_trivial) h.2]
  refine ⟨he, ?_⟩
  intro es hfree
  induction es with
  | nil => simp [compileExpsExact]
  | cons e es ih =>
    simp only [expsFree, Bool.and_eq_true_iff] at hfree
    simp only [compileExpsExact, he e hfree.1, ih hfree.2]

theorem prog_identity {width : Nat} [NeZero width] :
    ∀ (p : ProgHOL width) (context : ContextExact), progFree p = true → compileProgExact context p = p := by
  intro p
  induction p using (measure (sizeOf : ProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p → ∀ ctx, progFree q = true → compileProgExact ctx q = q at ih
    intro context h
    cases p with
    | skip | «break» | «continue» | tick | annot _ _ => simp [compileProgExact]
    | assign _ _ v | «return» v | raise _ v | shMemLoad _ _ _ v =>
      simp only [progFree] at h
      rw [compileProgExact, (exp_identity context).1 v h]
    | primitive _ _ args =>
      simp only [progFree] at h
      rw [compileProgExact, (exp_identity context).2 args h]
    | store a b | store32 a b | storeByte a b | shMemStore _ a b =>
      simp only [progFree, Bool.and_eq_true_iff] at h
      rw [compileProgExact, (exp_identity context).1 a h.1, (exp_identity context).1 b h.2]
    | dec _ sh v body =>
      simp only [progFree, Bool.and_eq_true_iff] at h
      rw [compileProgExact, (shape_identity context.structs).1 sh h.1.1,
        (exp_identity context).1 v h.1.2, ih body (by decreasing_trivial) _ h.2]
    | decCall _ sh _ args body =>
      simp only [progFree, Bool.and_eq_true_iff] at h
      rw [compileProgExact, (shape_identity context.structs).1 sh h.1.1,
        (exp_identity context).2 args h.1.2, ih body (by decreasing_trivial) _ h.2]
    | seq a b =>
      simp only [progFree, Bool.and_eq_true_iff] at h
      rw [compileProgExact, ih a (by decreasing_trivial) _ h.1, ih b (by decreasing_trivial) _ h.2]
    | ite c a b =>
      simp only [progFree, Bool.and_eq_true_iff] at h
      rw [compileProgExact, (exp_identity context).1 c h.1.1,
        ih a (by decreasing_trivial) _ h.1.2, ih b (by decreasing_trivial) _ h.2]
    | «while» c body =>
      simp only [progFree, Bool.and_eq_true_iff] at h
      rw [compileProgExact, (exp_identity context).1 c h.1, ih body (by decreasing_trivial) _ h.2]
    | extCall _ c cl a al =>
      simp only [progFree, Bool.and_eq_true_iff] at h
      rw [compileProgExact, (exp_identity context).1 c h.1.1.1,
        (exp_identity context).1 cl h.1.1.2, (exp_identity context).1 a h.1.2,
        (exp_identity context).1 al h.2]
    | call info _ args =>
      cases info with
      | none =>
        simp only [progFree] at h
        rw [compileProgExact, (exp_identity context).2 args h]
      | some inf =>
        rcases inf with ⟨rets, hdl⟩
        cases hdl with
        | none =>
          simp only [progFree] at h
          rw [compileProgExact, (exp_identity context).2 args h]
        | some hb =>
          rcases hb with ⟨ex, hv, body⟩
          simp only [progFree, Bool.and_eq_true_iff] at h
          rw [compileProgExact, (exp_identity context).2 args h.1,
            ih body (by simp_wf; omega) _ h.2]

theorem params_identity {α : Type} (context : List (MlS × List (α × ShapeHOL)))
    (params : List (MlS × ShapeHOL)) (h : params.all (fun p => shapeFree p.2) = true) :
    params.map (fun p => (p.1, compileShapeExact context p.2)) = params := by
  induction params with
  | nil => rfl
  | cons p params ih =>
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    simp only [List.map_cons, (shape_identity context).1 p.2 h.1, ih h.2]

theorem compileDeclsExact_fst_identity {width : Nat} [NeZero width] :
    ∀ (decls : List (DeclHOL width)) (ctx : ContextExact),
      decls.all declarationFree = true →
      (compileDeclsExact ctx decls).1 = decls
  | [], _, _ => by simp [compileDeclsExact]
  | d :: rest, ctx, h => by
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    rcases h with ⟨hd, hrest⟩
    cases d with
    | name _ _ => simp [declarationFree] at hd
    | exnDecl name shape =>
      simp only [declarationFree] at hd
      simp only [compileDeclsExact, (shape_identity ctx.structs).1 shape hd,
        compileDeclsExact_fst_identity rest ctx hrest]
    | decl shape name value =>
      simp only [declarationFree, Bool.and_eq_true_iff] at hd
      simp only [compileDeclsExact, (shape_identity ctx.structs).1 shape hd.1,
        (exp_identity ctx).1 value hd.2,
        compileDeclsExact_fst_identity rest { ctx with globals := (name, shape) :: ctx.globals } hrest]
    | function fn =>
      simp only [declarationFree, Bool.and_eq_true_iff] at hd
      simp only [compileDeclsExact, params_identity ctx.structs fn.params hd.1.1,
        prog_identity fn.body _ hd.1.2,
        (shape_identity ctx.structs).1 fn.returnShape hd.2,
        compileDeclsExact_fst_identity rest ctx hrest]

theorem compileTopExact_identity {width : Nat} [NeZero width]
    (decls : List (DeclHOL width)) (h : decls.all declarationFree = true) :
    compileTopExact decls = decls := by
  unfold compileTopExact
  exact compileDeclsExact_fst_identity decls _ h

/-! ## 3. Preservation of `declGood` Across `mainFirstHOL` and `panSimpDeclsHOL` -/

theorem smartSeqHOL_preserves {width : Nat} [NeZero width] (pre p : ProgHOL width) :
    panProgCost (smartSeqHOL pre p) = panProgCost pre + panProgCost p ∧
    (progFree pre = true → progFree p = true → progFree (smartSeqHOL pre p) = true) ∧
    (loadSafeProg pre = true → loadSafeProg p = true → loadSafeProg (smartSeqHOL pre p) = true) ∧
    (progNoGlobCall pre = true → progNoGlobCall p = true → progNoGlobCall (smartSeqHOL pre p) = true) := by
  have h1 : ∀ q, q ≠ ProgHOL.skip → smartSeqHOL q p = .seq q p := by
    intro q hq; cases q <;> first | exact absurd rfl hq | rfl
  by_cases hpre : pre = .skip
  · subst hpre
    simp [smartSeqHOL, panProgCost, progFree, loadSafeProg, progNoGlobCall]
  · rw [h1 pre hpre]
    refine ⟨rfl, ?_, ?_, ?_⟩ <;> intro ha hb <;>
      simp [progFree, loadSafeProg, progNoGlobCall, ha, hb]

theorem seqAssocHOL_preserves {width : Nat} [NeZero width] :
    ∀ (p pre : ProgHOL width),
      panProgCost (seqAssocHOL pre p) ≤ panProgCost pre + panProgCost p ∧
      (progFree pre = true → progFree p = true → progFree (seqAssocHOL pre p) = true) ∧
      (loadSafeProg pre = true → loadSafeProg p = true → loadSafeProg (seqAssocHOL pre p) = true) ∧
      (progNoGlobCall pre = true → progNoGlobCall p = true → progNoGlobCall (seqAssocHOL pre p) = true) := by
  intro p
  induction p using (measure (sizeOf : ProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p → ∀ pre,
      panProgCost (seqAssocHOL pre q) ≤ panProgCost pre + panProgCost q ∧
      (progFree pre = true → progFree q = true → progFree (seqAssocHOL pre q) = true) ∧
      (loadSafeProg pre = true → loadSafeProg q = true → loadSafeProg (seqAssocHOL pre q) = true) ∧
      (progNoGlobCall pre = true → progNoGlobCall q = true → progNoGlobCall (seqAssocHOL pre q) = true) at ih
    intro pre
    cases p with
    | skip =>
      rw [seqAssocHOL]
      refine ⟨by simp [panProgCost], fun h _ => h, fun h _ => h, fun h _ => h⟩
    | annot _ _ =>
      rw [seqAssocHOL]
      refine ⟨by simp [panProgCost], fun h _ => h, fun h _ => h, fun h _ => h⟩
    | seq a b =>
      rw [seqAssocHOL]
      have iha := ih a (by decreasing_trivial) pre
      have ihb := ih b (by decreasing_trivial) (seqAssocHOL pre a)
      refine ⟨by simp only [panProgCost]; omega, ?_, ?_, ?_⟩
      · intro hpre hp; simp only [progFree, Bool.and_eq_true_iff] at hp
        exact ihb.2.1 (iha.2.1 hpre hp.1) hp.2
      · intro hpre hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp
        exact ihb.2.2.1 (iha.2.2.1 hpre hp.1) hp.2
      · intro hpre hp; simp only [progNoGlobCall, Bool.and_eq_true_iff] at hp
        exact ihb.2.2.2 (iha.2.2.2 hpre hp.1) hp.2
    | dec n s v body =>
      rw [seqAssocHOL]
      have ihb := ih body (by decreasing_trivial) .skip
      have hs := smartSeqHOL_preserves pre (.dec n s v (seqAssocHOL .skip body))
      refine ⟨by have := hs.1; have := ihb.1; simp only [panProgCost] at *; omega, ?_, ?_, ?_⟩
      · intro hpre hp; simp only [progFree, Bool.and_eq_true_iff] at hp
        exact hs.2.1 hpre (by simp [progFree, hp.1.1, hp.1.2, ihb.2.1 rfl hp.2])
      · intro hpre hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp
        exact hs.2.2.1 hpre (by simp [loadSafeProg, hp.1, ihb.2.2.1 rfl hp.2])
      · intro hpre hp; simp only [progNoGlobCall] at hp
        exact hs.2.2.2 hpre (by simp [progNoGlobCall, ihb.2.2.2 rfl hp])
    | decCall n s f args body =>
      rw [seqAssocHOL]
      have ihb := ih body (by decreasing_trivial) .skip
      have hs := smartSeqHOL_preserves pre (.decCall n s f args (seqAssocHOL .skip body))
      refine ⟨by have := hs.1; have := ihb.1; simp only [panProgCost] at *; omega, ?_, ?_, ?_⟩
      · intro hpre hp; simp only [progFree, Bool.and_eq_true_iff] at hp
        exact hs.2.1 hpre (by simp [progFree, hp.1.1, hp.1.2, ihb.2.1 rfl hp.2])
      · intro hpre hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp
        exact hs.2.2.1 hpre (by simp [loadSafeProg, hp.1, ihb.2.2.1 rfl hp.2])
      · intro hpre hp; simp only [progNoGlobCall] at hp
        exact hs.2.2.2 hpre (by simp [progNoGlobCall, ihb.2.2.2 rfl hp])
    | ite c a b =>
      rw [seqAssocHOL]
      have iha := ih a (by decreasing_trivial) .skip
      have ihb := ih b (by decreasing_trivial) .skip
      have hs := smartSeqHOL_preserves pre (.ite c (seqAssocHOL .skip a) (seqAssocHOL .skip b))
      refine ⟨by have := hs.1; have := iha.1; have := ihb.1; simp only [panProgCost] at *; omega, ?_, ?_, ?_⟩
      · intro hpre hp; simp only [progFree, Bool.and_eq_true_iff] at hp
        exact hs.2.1 hpre (by simp [progFree, hp.1.1, iha.2.1 rfl hp.1.2, ihb.2.1 rfl hp.2])
      · intro hpre hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp
        exact hs.2.2.1 hpre (by simp [loadSafeProg, hp.1.1, iha.2.2.1 rfl hp.1.2, ihb.2.2.1 rfl hp.2])
      · intro hpre hp; simp only [progNoGlobCall, Bool.and_eq_true_iff] at hp
        exact hs.2.2.2 hpre (by simp [progNoGlobCall, iha.2.2.2 rfl hp.1, ihb.2.2.2 rfl hp.2])
    | «while» c body =>
      rw [seqAssocHOL]
      have ihb := ih body (by decreasing_trivial) .skip
      have hs := smartSeqHOL_preserves pre (.while c (seqAssocHOL .skip body))
      refine ⟨by have := hs.1; have := ihb.1; simp only [panProgCost] at *; omega, ?_, ?_, ?_⟩
      · intro hpre hp; simp only [progFree, Bool.and_eq_true_iff] at hp
        exact hs.2.1 hpre (by simp [progFree, hp.1, ihb.2.1 rfl hp.2])
      · intro hpre hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp
        exact hs.2.2.1 hpre (by simp [loadSafeProg, hp.1, ihb.2.2.1 rfl hp.2])
      · intro hpre hp; simp only [progNoGlobCall] at hp
        exact hs.2.2.2 hpre (by simp [progNoGlobCall, ihb.2.2.2 rfl hp])
    | call info f args =>
      cases info with
      | none =>
        simp only [seqAssocHOL]
        have hs := smartSeqHOL_preserves pre (.call none f args)
        exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
      | some inf =>
        rcases inf with ⟨rets, hdl⟩
        cases hdl with
        | none =>
          simp only [seqAssocHOL]
          have hs := smartSeqHOL_preserves pre (.call (some (rets, none)) f args)
          exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
        | some hb =>
          rcases hb with ⟨ex, hv, body⟩
          simp only [seqAssocHOL]
          have ihb := ih body (by simp_wf; omega) .skip
          have hs := smartSeqHOL_preserves pre (.call (some (rets, some (ex, hv, seqAssocHOL .skip body))) f args)
          refine ⟨by have := hs.1; have := ihb.1; simp only [panProgCost] at *; omega, ?_, ?_, ?_⟩
          · intro hpre hp; simp only [progFree, Bool.and_eq_true_iff] at hp
            exact hs.2.1 hpre (by simp [progFree, hp.1, ihb.2.1 rfl hp.2])
          · intro hpre hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp
            exact hs.2.2.1 hpre (by simp [loadSafeProg, hp.1, ihb.2.2.1 rfl hp.2])
          · intro hpre hp
            cases rets with
            | none =>
              simp only [progNoGlobCall] at hp
              exact hs.2.2.2 hpre (by simp [progNoGlobCall, ihb.2.2.2 rfl hp])
            | some rk =>
              rcases rk with ⟨vk, vn⟩
              cases vk with
              | «local» =>
                simp only [progNoGlobCall] at hp
                exact hs.2.2.2 hpre (by simp [progNoGlobCall, ihb.2.2.2 rfl hp])
              | global => simp [progNoGlobCall] at hp
    | assign k n e =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.assign k n e)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | primitive n o a =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.primitive n o a)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | store a v =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.store a v)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | store32 a v =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.store32 a v)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | storeByte a v =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.storeByte a v)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | «break» =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre .break
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | «continue» =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre .continue
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | extCall f c cl a al =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.extCall f c cl a al)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | raise e v =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.raise e v)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | «return» v =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.return v)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | shMemLoad s k n a =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.shMemLoad s k n a)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | shMemStore s a v =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre (.shMemStore s a v)
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩
    | tick =>
      simp only [seqAssocHOL]; have hs := smartSeqHOL_preserves pre .tick
      exact ⟨by simp [hs.1], hs.2.1, hs.2.2.1, hs.2.2.2⟩

theorem seqCallRetHOL_preserves {width : Nat} [NeZero width] (p : ProgHOL width) :
    panProgCost (seqCallRetHOL p) ≤ panProgCost p ∧
    (progFree p = true → progFree (seqCallRetHOL p) = true) ∧
    (loadSafeProg p = true → loadSafeProg (seqCallRetHOL p) = true) ∧
    (progNoGlobCall p = true → progNoGlobCall (seqCallRetHOL p) = true) := by
  unfold seqCallRetHOL
  split
  · split
    · refine ⟨by simp [panProgCost, panExpCost], ?_, ?_, ?_⟩
      · intro h; simp [progFree, expFree] at h ⊢; exact h
      · intro h; simp [loadSafeProg, loadSafeExp] at h ⊢; exact h
      · intro _; rfl
    · exact ⟨Nat.le_refl _, id, id, id⟩
  · exact ⟨Nat.le_refl _, id, id, id⟩

theorem retToTailHOL_preserves {width : Nat} [NeZero width] :
    ∀ p : ProgHOL width,
      panProgCost (retToTailHOL p) ≤ panProgCost p ∧
      (progFree p = true → progFree (retToTailHOL p) = true) ∧
      (loadSafeProg p = true → loadSafeProg (retToTailHOL p) = true) ∧
      (progNoGlobCall p = true → progNoGlobCall (retToTailHOL p) = true) := by
  intro p
  induction p using (measure (sizeOf : ProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p →
      panProgCost (retToTailHOL q) ≤ panProgCost q ∧
      (progFree q = true → progFree (retToTailHOL q) = true) ∧
      (loadSafeProg q = true → loadSafeProg (retToTailHOL q) = true) ∧
      (progNoGlobCall q = true → progNoGlobCall (retToTailHOL q) = true) at ih
    cases p with
    | dec n s v b =>
      rw [retToTailHOL]; have ihb := ih b (by decreasing_trivial)
      refine ⟨by simp only [panProgCost]; have := ihb.1; omega, ?_, ?_, ?_⟩
      · intro hp; simp only [progFree, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.1 hp.2⟩
      · intro hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.2.1 hp.2⟩
      · intro hp; simp only [progNoGlobCall] at hp ⊢; exact ihb.2.2.2 hp
    | seq a b =>
      rw [retToTailHOL]
      have iha := ih a (by decreasing_trivial)
      have ihb := ih b (by decreasing_trivial)
      have hs := seqCallRetHOL_preserves (.seq (retToTailHOL a) (retToTailHOL b))
      refine ⟨by have := hs.1; have := iha.1; have := ihb.1; simp only [panProgCost] at *; omega, ?_, ?_, ?_⟩
      · intro hp; simp only [progFree, Bool.and_eq_true_iff] at hp
        exact hs.2.1 (by simp [progFree, iha.2.1 hp.1, ihb.2.1 hp.2])
      · intro hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp
        exact hs.2.2.1 (by simp [loadSafeProg, iha.2.2.1 hp.1, ihb.2.2.1 hp.2])
      · intro hp; simp only [progNoGlobCall, Bool.and_eq_true_iff] at hp
        exact hs.2.2.2 (by simp [progNoGlobCall, iha.2.2.2 hp.1, ihb.2.2.2 hp.2])
    | ite c a b =>
      rw [retToTailHOL]
      have iha := ih a (by decreasing_trivial)
      have ihb := ih b (by decreasing_trivial)
      refine ⟨by have := iha.1; have := ihb.1; simp only [panProgCost]; omega, ?_, ?_, ?_⟩
      · intro hp; simp only [progFree, Bool.and_eq_true_iff] at hp ⊢
        exact ⟨⟨hp.1.1, iha.2.1 hp.1.2⟩, ihb.2.1 hp.2⟩
      · intro hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp ⊢
        exact ⟨⟨hp.1.1, iha.2.2.1 hp.1.2⟩, ihb.2.2.1 hp.2⟩
      · intro hp; simp only [progNoGlobCall, Bool.and_eq_true_iff] at hp ⊢
        exact ⟨iha.2.2.2 hp.1, ihb.2.2.2 hp.2⟩
    | «while» c body =>
      rw [retToTailHOL]; have ihb := ih body (by decreasing_trivial)
      refine ⟨by have := ihb.1; simp only [panProgCost]; omega, ?_, ?_, ?_⟩
      · intro hp; simp only [progFree, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.1 hp.2⟩
      · intro hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.2.1 hp.2⟩
      · intro hp; simp only [progNoGlobCall] at hp ⊢; exact ihb.2.2.2 hp
    | decCall n s f args body =>
      rw [retToTailHOL]; have ihb := ih body (by decreasing_trivial)
      refine ⟨by have := ihb.1; simp only [panProgCost]; omega, ?_, ?_, ?_⟩
      · intro hp; simp only [progFree, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.1 hp.2⟩
      · intro hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.2.1 hp.2⟩
      · intro hp; simp only [progNoGlobCall] at hp ⊢; exact ihb.2.2.2 hp
    | call info f args =>
      cases info with
      | none => simp only [retToTailHOL]; exact ⟨Nat.le_refl _, id, id, id⟩
      | some inf =>
        rcases inf with ⟨rets, hdl⟩
        cases hdl with
        | none => simp only [retToTailHOL]; exact ⟨Nat.le_refl _, id, id, id⟩
        | some hb =>
          rcases hb with ⟨ex, hv, body⟩
          simp only [retToTailHOL]
          have ihb := ih body (by simp_wf; omega)
          refine ⟨by have := ihb.1; simp only [panProgCost]; omega, ?_, ?_, ?_⟩
          · intro hp; simp only [progFree, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.1 hp.2⟩
          · intro hp; simp only [loadSafeProg, Bool.and_eq_true_iff] at hp ⊢; exact ⟨hp.1, ihb.2.2.1 hp.2⟩
          · intro hp
            cases rets with
            | none => simp only [progNoGlobCall] at hp ⊢; exact ihb.2.2.2 hp
            | some rk =>
              rcases rk with ⟨vk, vn⟩
              cases vk with
              | «local» => simp only [progNoGlobCall] at hp ⊢; exact ihb.2.2.2 hp
              | global => simp [progNoGlobCall] at hp
    | skip | annot _ _ | assign _ _ _ | primitive _ _ _ | store _ _ | store32 _ _ | storeByte _ _
    | «break» | «continue» | extCall _ _ _ _ _ | raise _ _ | «return» _ | shMemLoad _ _ _ _ | shMemStore _ _ _ | tick =>
      simp only [retToTailHOL]; exact ⟨Nat.le_refl _, id, id, id⟩

theorem panSimpCompileHOL_preserves {width : Nat} [NeZero width] (p : ProgHOL width) :
    panProgCost (panSimpCompileHOL p) ≤ panProgCost p ∧
    (progFree p = true → progFree (panSimpCompileHOL p) = true) ∧
    (loadSafeProg p = true → loadSafeProg (panSimpCompileHOL p) = true) ∧
    (progNoGlobCall p = true → progNoGlobCall (panSimpCompileHOL p) = true) := by
  unfold panSimpCompileHOL
  have hsa := seqAssocHOL_preserves p .skip
  have hrt := retToTailHOL_preserves (seqAssocHOL .skip p)
  refine ⟨by have := hsa.1; have := hrt.1; simp only [panProgCost] at *; omega, ?_, ?_, ?_⟩
  · intro hp; exact hrt.2.1 (hsa.2.1 rfl hp)
  · intro hp; exact hrt.2.2.1 (hsa.2.2.1 rfl hp)
  · intro hp; exact hrt.2.2.2 (hsa.2.2.2 rfl hp)

theorem panSimpDeclsHOL_good {width : Nat} [NeZero width] :
    ∀ decls : List (DeclHOL width),
      decls.all declGood = true →
      (panSimpDeclsHOL decls).all declGood = true
  | [], _ => by simp [panSimpDeclsHOL]
  | d :: ds, h => by
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    rcases h with ⟨hd, hds⟩
    cases d with
    | function fn =>
      simp only [panSimpDeclsHOL, List.all_cons, Bool.and_eq_true_iff, panSimpDeclsHOL_good ds hds, and_true]
      simp only [declGood, declarationFree, Bool.and_eq_true_iff, decide_eq_true_eq] at hd ⊢
      have hp := panSimpCompileHOL_preserves fn.body
      refine ⟨⟨⟨⟨hd.1.1.1.1, ⟨⟨hd.1.1.1.2.1.1, hp.2.1 hd.1.1.1.2.1.2⟩, hd.1.1.1.2.2⟩⟩,
        hp.2.2.1 hd.1.1.2⟩, hp.2.2.2 hd.1.2⟩, Nat.le_trans hp.1 hd.2⟩
    | decl sh n v =>
      simp only [panSimpDeclsHOL, List.all_cons, Bool.and_eq_true_iff]; exact ⟨hd, panSimpDeclsHOL_good ds hds⟩
    | exnDecl n sh =>
      simp only [panSimpDeclsHOL, List.all_cons, Bool.and_eq_true_iff]; exact ⟨hd, panSimpDeclsHOL_good ds hds⟩
    | name n fs =>
      simp only [panSimpDeclsHOL, List.all_cons, Bool.and_eq_true_iff]; exact ⟨hd, panSimpDeclsHOL_good ds hds⟩

theorem span_loop_all {α : Type} (p q : α → Bool) :
    ∀ (xs acc : List α), xs.all q = true → acc.all q = true →
      (List.span.loop p xs acc).1.all q = true ∧ (List.span.loop p xs acc).2.all q = true
  | [], acc, _, hacc => by
    simp [List.span.loop, List.all_reverse, hacc]
  | x :: xs, acc, hxs, hacc => by
    simp only [List.all_cons, Bool.and_eq_true_iff] at hxs
    simp only [List.span.loop]
    cases p x with
    | true =>
      exact span_loop_all p q xs (x :: acc) hxs.2 (by simp [hxs.1, hacc])
    | false =>
      simp [List.all_reverse, hacc, hxs.1, hxs.2]

theorem span_all {α : Type} (p q : α → Bool) (xs : List α) (h : xs.all q = true) :
    (xs.span p).1.all q = true ∧ (xs.span p).2.all q = true :=
  span_loop_all p q xs [] h rfl

theorem mainFirstHOL_good {width : Nat} [NeZero width]
    (decls : List (DeclHOL width)) (h : decls.all declGood = true) :
    (Pancake.PanToTarget.mainFirstHOL decls).all declGood = true := by
  unfold Pancake.PanToTarget.mainFirstHOL
  have hsp := span_all (fun declaration =>
    match declaration with
    | .function entry => decide (entry.name ≠ ofString "main")
    | _ => true) declGood decls h
  generalize decls.span (fun declaration =>
    match declaration with
    | .function entry => decide (entry.name ≠ ofString "main")
    | _ => true) = sp at hsp ⊢
  rcases sp with ⟨before, after⟩
  cases before with
  | nil => exact hsp.2
  | cons b bs =>
    cases after with
    | nil =>
      simp only [List.all_cons, Bool.and_eq_true_iff, hsp.1, and_true]
      simp [declGood, declarationFree, progFree, expFree, shapeFree, loadSafeProg,
        loadSafeExp, progNoGlobCall, panProgCost, panExpCost]
    | cons m rest =>
      simp only [List.all_cons, List.all_append, Bool.and_eq_true_iff] at hsp ⊢
      tauto

theorem declGood_imp_free {width : Nat} [NeZero width] (d : DeclHOL width) (h : declGood d = true) :
    declarationFree d = true := by
  cases d <;> simp [declGood, declarationFree] at h ⊢ <;> tauto

theorem all_declGood_imp_all_free {width : Nat} [NeZero width] (decls : List (DeclHOL width))
    (h : decls.all declGood = true) : decls.all declarationFree = true := by
  rw [List.all_eq_true] at h ⊢
  intro d hd
  exact declGood_imp_free d (h d hd)

/-! ## 4. Preservation Across `PanGlobals` (`compileTopExactHOL`) -/

def ctxAllShapeOne {width : Nat} [NeZero width] (ctx : PanGlobalsContextExact width) : Prop :=
  ∀ name sh addr, ctx.globals.lookup name = some (sh, addr) → sh = .one

theorem fpermHOL_preserves {width : Nat} [NeZero width] (f g : MlS) :
    ∀ p : ProgHOL width,
      panProgCost (fpermHOL f g p) = panProgCost p ∧
      loadSafeProg (fpermHOL f g p) = loadSafeProg p ∧
      progNoGlobCall (fpermHOL f g p) = progNoGlobCall p := by
  intro p
  induction p using (measure (sizeOf : ProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p →
      panProgCost (fpermHOL f g q) = panProgCost q ∧
      loadSafeProg (fpermHOL f g q) = loadSafeProg q ∧
      progNoGlobCall (fpermHOL f g q) = progNoGlobCall q at ih
    rw [InitECandidate.Proofs.GlobalsKernelComputation.fperm_eq]
    cases p with
    | dec _ _ _ b =>
      have ihb := ih b (by decreasing_trivial)
      rw [InitECandidate.Proofs.GlobalsKernelComputation.fperm_eq] at ihb
      simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall, ihb]
    | seq a b =>
      have iha := ih a (by decreasing_trivial)
      have ihb := ih b (by decreasing_trivial)
      rw [InitECandidate.Proofs.GlobalsKernelComputation.fperm_eq] at iha ihb
      simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall, iha, ihb]
    | ite _ a b =>
      have iha := ih a (by decreasing_trivial)
      have ihb := ih b (by decreasing_trivial)
      rw [InitECandidate.Proofs.GlobalsKernelComputation.fperm_eq] at iha ihb
      simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall, iha, ihb]
    | «while» _ b =>
      have ihb := ih b (by decreasing_trivial)
      rw [InitECandidate.Proofs.GlobalsKernelComputation.fperm_eq] at ihb
      simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall, ihb]
    | decCall _ _ _ _ b =>
      have ihb := ih b (by decreasing_trivial)
      rw [InitECandidate.Proofs.GlobalsKernelComputation.fperm_eq] at ihb
      simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall, ihb]
    | call info _ _ =>
      cases info with
      | none => simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall]
      | some inf =>
        rcases inf with ⟨rk, hdl⟩
        cases hdl with
        | none =>
          cases rk with
          | none => simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall]
          | some rkv =>
            rcases rkv with ⟨vk, _⟩
            cases vk <;> simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall]
        | some hb =>
          rcases hb with ⟨eid, ev, body⟩
          have ihb := ih body (by simp_wf; omega)
          rw [InitECandidate.Proofs.GlobalsKernelComputation.fperm_eq] at ihb
          cases rk with
          | none => simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall, ihb]
          | some rkv =>
            rcases rkv with ⟨vk, _⟩
            cases vk <;> simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall, ihb]
    | shMemLoad _ vk _ _ =>
      cases vk <;> simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall]
    | _ => simp [InitECandidate.Proofs.GlobalsKernelComputation.fpermHOL, panProgCost, loadSafeProg, progNoGlobCall]

theorem globals_compileExp_preserves {width : Nat} [NeZero width]
    (ctx : PanGlobalsContextExact width) :
    (∀ e : ExpHOL width,
      panExpCost (Flapjack.compileExpExactHOL ctx e) ≤ panExpCost e ∧
      (loadSafeExp e = true → loadSafeExp (Flapjack.compileExpExactHOL ctx e) = true)) ∧
    (∀ es : List (ExpHOL width),
      panExpsCost (Flapjack.compileExpExactHOLList ctx es) ≤ panExpsCost es ∧
      (loadSafeExps es = true → loadSafeExps (Flapjack.compileExpExactHOLList ctx es) = true)) := by
  have he : ∀ e : ExpHOL width,
      panExpCost (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL ctx e) ≤ panExpCost e ∧
      (loadSafeExp e = true → loadSafeExp (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL ctx e) = true) := by
    intro e
    induction e using (measure (sizeOf : ExpHOL width → Nat)).wf.induction with
    | h e ih =>
      change ∀ c, sizeOf c < sizeOf e →
        panExpCost (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL ctx c) ≤ panExpCost c ∧
        (loadSafeExp c = true → loadSafeExp (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL ctx c) = true) at ih
      have ihm : ∀ es : List (ExpHOL width), (∀ x ∈ es, sizeOf x < sizeOf e) →
          panExpsCost (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOLList ctx es) ≤ panExpsCost es ∧
          (loadSafeExps es = true → loadSafeExps (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOLList ctx es) = true) := by
        intro es hes
        induction es with
        | nil => simp [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOLList, panExpsCost, loadSafeExps]
        | cons x xs ihxs =>
          have ihx := ih x (hes x List.mem_cons_self)
          have ihrest := ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy))
          simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOLList, panExpsCost, loadSafeExps, Bool.and_eq_true_iff]
          exact ⟨Nat.add_le_add ihx.1 ihrest.1, fun h => ⟨ihx.2 h.1, ihrest.2 h.2⟩⟩
      cases e with
      | const _ | baseAddr | bytesInWord =>
        simp [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp]
      | topAddr =>
        simp [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, panExpsCost, loadSafeExp, loadSafeExps]
      | var vk vn =>
        cases vk with
        | «local» => simp [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp]
        | global =>
          simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL]
          cases ctx.globals.lookup vn with
          | none => simp [panExpCost, loadSafeExp]
          | some p => simp [panExpCost, panExpsCost, loadSafeExp, loadSafeExps]
      | nstruct _ _ | nfield _ _ =>
        simp [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp]
      | rstruct es | op _ es | panop _ es =>
        have h := ihm es (by intros; sizeOf_list_dec)
        simpa [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp] using h
      | rfield _ v | load32 v | loadByte v =>
        have h := ih v (by decreasing_trivial)
        simpa [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp] using h
      | load sh addr =>
        have h := ih addr (by decreasing_trivial)
        simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp,
          Bool.and_eq_true_iff, Bool.or_eq_true, decide_eq_true_eq]
        refine ⟨h.1, fun hs => ⟨?_, h.2 hs.2⟩⟩
        rcases hs.1 with hsh | hcost
        · exact Or.inl hsh
        · have h0 : panExpCost (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL ctx addr) = 0 := by
            have := h.1; omega
          exact Or.inr h0
      | cmp _ l r =>
        have hl := ih l (by decreasing_trivial)
        have hr := ih r (by decreasing_trivial)
        simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp, Bool.and_eq_true_iff]
        exact ⟨by have := hl.1; have := hr.1; omega, fun h => ⟨hl.2 h.1, hr.2 h.2⟩⟩
      | shift _ l r =>
        have hl := ih l (by decreasing_trivial)
        have hr := ih r (by decreasing_trivial)
        simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL, panExpCost, loadSafeExp, Bool.and_eq_true_iff]
        exact ⟨by have := hl.1; have := hr.1; omega, fun h => ⟨hl.2 h.1, hr.2 h.2⟩⟩
  refine ⟨fun e => ?_, fun es => ?_⟩
  · rw [InitECandidate.Proofs.GlobalsKernelComputation.compileExp_eq]
    exact he e
  · rw [InitECandidate.Proofs.GlobalsKernelComputation.compileExpList_function_eq]
    induction es with
    | nil => simp [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOLList, panExpsCost, loadSafeExps]
    | cons x xs ih =>
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOLList, panExpsCost, loadSafeExps, Bool.and_eq_true_iff]
      exact ⟨Nat.add_le_add (he x).1 ih.1, fun h => ⟨(he x).2 h.1, ih.2 h.2⟩⟩

theorem globals_compileProg_preserves {width : Nat} [NeZero width]
    (ctx : PanGlobalsContextExact width) :
    ∀ p : ProgHOL width,
      progNoGlobCall p = true →
      loadSafeProg p = true →
      panProgCost (Flapjack.compileProgExactHOL ctx p) ≤ panProgCost p ∧
      loadSafeProg (Flapjack.compileProgExactHOL ctx p) = true := by
  intro p
  rw [InitECandidate.Proofs.GlobalsKernelComputation.compileProg_eq]
  induction p using (measure (sizeOf : ProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p →
      progNoGlobCall q = true →
      loadSafeProg q = true →
      panProgCost (InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL ctx q) ≤ panProgCost q ∧
      loadSafeProg (InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL ctx q) = true at ih
    intro hng hls
    have he := (globals_compileExp_preserves ctx).1
    have hes := (globals_compileExp_preserves ctx).2
    simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileExp_function_eq,
      InitECandidate.Proofs.GlobalsKernelComputation.compileExpList_function_eq] at he hes
    cases p with
    | skip | «break» | «continue» | tick | annot _ _ =>
      simp [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
    | assign vk n v =>
      cases vk with
      | «local» =>
        simp only [loadSafeProg] at hls
        simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
        exact ⟨(he v).1, (he v).2 hls⟩
      | global =>
        simp only [loadSafeProg] at hls
        simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL]
        cases ctx.globals.lookup n with
        | none => simp [panProgCost, loadSafeProg]
        | some p =>
          simp only [panProgCost, panExpCost, panExpsCost, loadSafeProg, loadSafeExp, loadSafeExps, Bool.true_and, Nat.zero_add]
          exact ⟨(he v).1, (he v).2 hls⟩
    | «return» v | raise _ v =>
      simp only [loadSafeProg] at hls
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
      exact ⟨(he v).1, (he v).2 hls⟩
    | shMemLoad s vk n a =>
      cases vk with
      | «local» =>
        simp only [loadSafeProg] at hls
        simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
        exact ⟨(he a).1, (he a).2 hls⟩
      | global => simp [progNoGlobCall] at hng
    | primitive _ _ args =>
      simp only [loadSafeProg] at hls
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
      exact ⟨(hes args).1, (hes args).2 hls⟩
    | store a b | store32 a b | storeByte a b | shMemStore _ a b =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
      exact ⟨Nat.add_le_add (he a).1 (he b).1, (he a).2 hls.1, (he b).2 hls.2⟩
    | extCall _ e1 e2 e3 e4 =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
      have h1 := he e1; have h2 := he e2; have h3 := he e3; have h4 := he e4
      exact ⟨by omega, ⟨⟨⟨h1.2 hls.1.1.1, h2.2 hls.1.1.2⟩, h3.2 hls.1.2⟩, h4.2 hls.2⟩⟩
    | dec _ _ e body =>
      simp only [progNoGlobCall] at hng
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have ihb := ih body (by decreasing_trivial) hng hls.2
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
      exact ⟨Nat.add_le_add (he e).1 ihb.1, (he e).2 hls.1, ihb.2⟩
    | decCall _ _ _ args body =>
      simp only [progNoGlobCall] at hng
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have ihb := ih body (by decreasing_trivial) hng hls.2
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
      have ha := (hes args).1; have hb := ihb.1
      exact ⟨by omega, (hes args).2 hls.1, ihb.2⟩
    | seq a b =>
      simp only [progNoGlobCall, Bool.and_eq_true_iff] at hng
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have iha := ih a (by decreasing_trivial) hng.1 hls.1
      have ihb := ih b (by decreasing_trivial) hng.2 hls.2
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
      exact ⟨Nat.add_le_add iha.1 ihb.1, iha.2, ihb.2⟩
    | ite c a b =>
      simp only [progNoGlobCall, Bool.and_eq_true_iff] at hng
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have iha := ih a (by decreasing_trivial) hng.1 hls.1.2
      have ihb := ih b (by decreasing_trivial) hng.2 hls.2
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
      have hc := (he c).1; have ha := iha.1; have hb := ihb.1
      exact ⟨by omega, ⟨(he c).2 hls.1.1, iha.2⟩, ihb.2⟩
    | «while» c body =>
      simp only [progNoGlobCall] at hng
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have ihb := ih body (by decreasing_trivial) hng hls.2
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
      have hc := (he c).1; have hb := ihb.1
      exact ⟨by omega, (he c).2 hls.1, ihb.2⟩
    | call info f args =>
      cases info with
      | none =>
        simp only [loadSafeProg] at hls
        simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
        have ha := (hes args).1
        exact ⟨by omega, (hes args).2 hls⟩
      | some inf =>
        rcases inf with ⟨rk, hdl⟩
        cases rk with
        | none =>
          cases hdl with
          | none =>
            simp only [loadSafeProg] at hls
            simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
            have ha := (hes args).1
            exact ⟨by omega, (hes args).2 hls⟩
          | some hb =>
            rcases hb with ⟨ex, hv, body⟩
            simp only [progNoGlobCall] at hng
            simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
            have ihb := ih body (by simp_wf; omega) hng hls.2
            simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
            have ha := (hes args).1; have hb' := ihb.1
            exact ⟨by omega, (hes args).2 hls.1, ihb.2⟩
        | some rkv =>
          rcases rkv with ⟨vk, vn⟩
          cases vk with
          | global =>
            cases hdl with
            | some _ => simp [progNoGlobCall] at hng
            | none =>
              simp only [loadSafeProg] at hls
              simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL]
              cases ctx.globals.lookup vn with
              | none =>
                simp only [panProgCost, loadSafeProg]
                have ha := (hes args).1
                exact ⟨by omega, (hes args).2 hls⟩
              | some gp =>
                rcases gp with ⟨sh, addr⟩
                have ha := (hes args).1
                have hsa := (hes args).2 hls
                refine ⟨?_, ?_⟩
                · simp only [panProgCost, panExpCost, panExpsCost]; omega
                · simp [loadSafeProg, loadSafeExp, loadSafeExps, hsa]
          | «local» =>
            cases hdl with
            | none =>
              simp only [loadSafeProg] at hls
              simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg]
              have ha := (hes args).1
              exact ⟨by omega, (hes args).2 hls⟩
            | some hb =>
              rcases hb with ⟨ex, hv, body⟩
              simp only [progNoGlobCall] at hng
              simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
              have ihb := ih body (by simp_wf; omega) hng hls.2
              simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileProgExactHOL, panProgCost, loadSafeProg, Bool.and_eq_true_iff]
              have ha := (hes args).1; have hb' := ihb.1
              exact ⟨by omega, (hes args).2 hls.1, ihb.2⟩

def declGlobalsGood {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .function fn =>
      !fn.inline &&
      loadSafeProg fn.body &&
      progNoGlobCall fn.body &&
      decide (panProgCost fn.body ≤ 448)
  | .decl _ _ value =>
      loadSafeExp value && decide (panExpCost value = 0)
  | .exnDecl _ _ => true
  | .name _ _ => false

theorem declGood_imp_globalsGood {width : Nat} [NeZero width] (d : DeclHOL width)
    (h : declGood d = true) : declGlobalsGood d = true := by
  cases d <;> simp [declGood, declGlobalsGood] at h ⊢ <;> tauto

theorem all_declGood_imp_globalsGood {width : Nat} [NeZero width] (decls : List (DeclHOL width))
    (h : decls.all declGood = true) : decls.all declGlobalsGood = true := by
  rw [List.all_eq_true] at h ⊢
  intro d hd
  exact declGood_imp_globalsGood d (h d hd)

def fnPostGlobalsGood {width : Nat} [NeZero width] : DeclHOL width → Bool
  | .function fn => !fn.inline && loadSafeProg fn.body && decide (panProgCost fn.body ≤ 448)
  | .exnDecl _ _ => true
  | _ => false

theorem nestedSeqHOL_zero_safe {width : Nat} [NeZero width] :
    ∀ inits : List (ProgHOL width),
      (∀ p ∈ inits, panProgCost p = 0 ∧ loadSafeProg p = true) →
      panProgCost (nestedSeqHOL inits) = 0 ∧ loadSafeProg (nestedSeqHOL inits) = true
  | [], _ => ⟨rfl, rfl⟩
  | p :: ps, h => by
    have hp := h p List.mem_cons_self
    have hps := nestedSeqHOL_zero_safe ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
    simp [nestedSeqHOL, panProgCost, loadSafeProg, hp.1, hp.2, hps.1, hps.2]

theorem compileDecsExactHOL_preserves {width : Nat} [NeZero width] :
    ∀ (decls : List (DeclHOL width)) (ctx : PanGlobalsContextExact width),
      decls.all declGlobalsGood = true →
      (∀ p ∈ (Flapjack.compileDecsExactHOL ctx decls).1, panProgCost p = 0 ∧ loadSafeProg p = true) ∧
      (Flapjack.compileDecsExactHOL ctx decls).2.1.all fnPostGlobalsGood = true ∧
      (Flapjack.compileDecsExactHOL ctx decls).2.2.1.all fnPostGlobalsGood = true
  | [], _, _ => by
    rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_eq]
    simp [InitECandidate.Proofs.GlobalsKernelComputation.compileDecsExactHOL]
  | d :: ds, ctx, h => by
    rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_eq]
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    rcases h with ⟨hd, hds⟩
    cases d with
    | name _ _ => simp [declGlobalsGood] at hd
    | exnDecl n sh =>
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileDecsExactHOL]
      have ih := compileDecsExactHOL_preserves ds ctx hds
      rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_eq] at ih
      refine ⟨ih.1, ih.2.1, ?_⟩
      simp [List.all_cons, fnPostGlobalsGood, ih.2.2]
    | decl sh n v =>
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileDecsExactHOL]
      simp only [declGlobalsGood, Bool.and_eq_true_iff, decide_eq_true_eq] at hd
      let address := ctx.globalsSize + cakeBytesInWord width * BitVec.ofNat width (sizeOfShapeHOL sh)
      let nextCtx : PanGlobalsContextExact width := {
        ctx with
        globals := ctx.globals.updateEq (n, (sh, address))
        globalsSize := address
      }
      have ih := compileDecsExactHOL_preserves ds nextCtx hds
      rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_eq] at ih
      refine ⟨?_, ih.2.1, ih.2.2⟩
      intro p hp
      rcases List.mem_cons.mp hp with rfl | htail
      · have he := (globals_compileExp_preserves ctx).1 v
        rw [InitECandidate.Proofs.GlobalsKernelComputation.compileExp_eq] at he
        have hcost0 : panExpCost (InitECandidate.Proofs.GlobalsKernelComputation.compileExpExactHOL ctx v) = 0 := by
          have := he.1; have := hd.2; omega
        simp [panProgCost, panExpCost, panExpsCost, loadSafeProg, loadSafeExp, loadSafeExps,
          hcost0, he.2 hd.1]
      · exact ih.1 p htail
    | function fn =>
      simp only [InitECandidate.Proofs.GlobalsKernelComputation.compileDecsExactHOL]
      simp only [declGlobalsGood, Bool.and_eq_true_iff, decide_eq_true_eq] at hd
      have ih := compileDecsExactHOL_preserves ds ctx hds
      rw [InitECandidate.Proofs.GlobalsKernelComputation.compileDecs_eq] at ih
      have hp := globals_compileProg_preserves ctx fn.body hd.1.2 hd.1.1.2
      rw [InitECandidate.Proofs.GlobalsKernelComputation.compileProg_eq] at hp
      refine ⟨ih.1, ?_, ih.2.2⟩
      simp only [List.all_cons, Bool.and_eq_true_iff, ih.2.1, and_true, fnPostGlobalsGood, decide_eq_true_eq]
      exact ⟨⟨hd.1.1.1, hp.2⟩, Nat.le_trans hp.1 hd.2⟩

theorem filter_all_pred {α : Type} (p q : α → Bool)
    (xs : List α) (h : xs.all q = true) :
    (xs.filter p).all q = true := by
  rw [List.all_eq_true] at h ⊢
  intro x hx
  exact h x (List.mem_filter.mp hx).1

theorem resortDeclsHOL_globalsGood {width : Nat} [NeZero width]
    (decls : List (DeclHOL width)) (h : decls.all declGlobalsGood = true) :
    (resortDeclsHOL decls).all declGlobalsGood = true := by
  unfold resortDeclsHOL
  simp only [List.all_append, Bool.and_eq_true_iff]
  exact ⟨⟨⟨filter_all_pred _ _ _ h, filter_all_pred _ _ _ h⟩,
    filter_all_pred _ _ _ h⟩, filter_all_pred _ _ _ h⟩

theorem fpermDecsHOL_globalsGood {width : Nat} [NeZero width] (f g : MlS) :
    ∀ decls : List (DeclHOL width),
      decls.all declGlobalsGood = true →
      (fpermDecsHOL f g decls).all declGlobalsGood = true
  | [], _ => by simp [fpermDecsHOL]
  | d :: ds, h => by
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    cases d with
    | function fn =>
      simp only [fpermDecsHOL, List.all_cons, Bool.and_eq_true_iff, fpermDecsHOL_globalsGood f g ds h.2, and_true]
      have hfp := fpermHOL_preserves f g fn.body
      simp only [declGlobalsGood, hfp.1, hfp.2.1, hfp.2.2] at h ⊢
      exact h.1
    | decl _ _ _ =>
      simp only [fpermDecsHOL, List.all_cons, Bool.and_eq_true_iff]
      exact ⟨h.1, fpermDecsHOL_globalsGood f g ds h.2⟩
    | exnDecl _ _ =>
      simp only [fpermDecsHOL, List.all_cons, Bool.and_eq_true_iff]
      exact ⟨h.1, fpermDecsHOL_globalsGood f g ds h.2⟩
    | name _ _ =>
      simp only [fpermDecsHOL, List.all_cons, Bool.and_eq_true_iff]
      exact ⟨h.1, fpermDecsHOL_globalsGood f g ds h.2⟩

theorem varLocalParams_zero_safe {width : Nat} [NeZero width] :
    ∀ params : List (MlS × ShapeHOL),
      panExpsCost (params.map fun entry => ExpHOL.var (width := width) .local entry.1) = 0 ∧
      loadSafeExps (params.map fun entry => ExpHOL.var (width := width) .local entry.1) = true
  | [] => ⟨rfl, rfl⟩
  | _ :: ps => by
    have ih := varLocalParams_zero_safe (width := width) ps
    simp [panExpsCost, panExpCost, loadSafeExps, loadSafeExp, ih.1, ih.2]

theorem compileTopExactHOL_good {width : Nat} [NeZero width]
    (decls : List (DeclHOL width)) (start : MlS)
    (h : decls.all declGlobalsGood = true) :
    (compileTopExactHOL decls start).all fnPostGlobalsGood = true := by
  unfold compileTopExactHOL
  split
  · rfl
  · rename_i _ arguments _body returnShape _
    dsimp only
    have hres := resortDeclsHOL_globalsGood decls h
    have hren := fpermDecsHOL_globalsGood start (newMainNameHOL decls) (resortDeclsHOL decls) hres
    have hdecs := compileDecsExactHOL_preserves
      (fpermDecsHOL start (newMainNameHOL decls) (resortDeclsHOL decls))
      { globals := HolFiniteMapExact.empty
        globalsSize := 0
        maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width
          ((decShapesHOL (fpermDecsHOL start (newMainNameHOL decls) (resortDeclsHOL decls))).map sizeOfShapeHOL).sum }
      hren
    rcases hcomp : Flapjack.compileDecsExactHOL _ _ with ⟨initializers, functions, exceptions, _ctx⟩
    rw [hcomp] at hdecs
    dsimp only at hdecs ⊢
    have hinits := nestedSeqHOL_zero_safe initializers hdecs.1
    have hparams := varLocalParams_zero_safe (width := width) arguments
    simp only [List.all_append, List.all_cons, Bool.and_eq_true_iff]
    refine ⟨hdecs.2.2, ?_, hdecs.2.1⟩
    simp [fnPostGlobalsGood, loadSafeProg, panProgCost, hinits.1, hinits.2, hparams.1, hparams.2]

/-! ## 5. PanToCrep Cost Upper Bound (`programCost (compFuncExactHOLW ...) ≤ panProgCost body`) -/

theorem expressionsCost_append {width : Nat} [NeZero width] (xs ys : List (CrepExpHOL width)) :
    expressionsCost (xs ++ ys) = expressionsCost xs + expressionsCost ys := by
  induction xs with
  | nil => simp [expressionsCost]
  | cons x xs ih => simp [expressionsCost, ih, Nat.add_assoc]

theorem expressionsCost_take {width : Nat} [NeZero width] :
    ∀ (n : Nat) (xs : List (CrepExpHOL width)), expressionsCost (xs.take n) ≤ expressionsCost xs
  | 0, _ => by simp [expressionsCost]
  | _ + 1, [] => by simp [expressionsCost]
  | n + 1, x :: xs => by
    simp only [List.take_succ_cons, expressionsCost]
    exact Nat.add_le_add_left (expressionsCost_take n xs) _

theorem expressionsCost_drop {width : Nat} [NeZero width] :
    ∀ (n : Nat) (xs : List (CrepExpHOL width)), expressionsCost (xs.drop n) ≤ expressionsCost xs
  | 0, _ => Nat.le_refl _
  | _ + 1, [] => by simp [expressionsCost]
  | n + 1, x :: xs => by
    simp only [List.drop_succ_cons, expressionsCost]
    exact Nat.le_trans (expressionsCost_drop n xs) (Nat.le_add_left _ _)

theorem compFieldHOL_cost {width : Nat} [NeZero width] :
    ∀ (idx : Nat) (shapes : List ShapeHOL) (es : List (CrepExpHOL width)),
      expressionsCost (compFieldHOL idx shapes es).1 ≤ expressionsCost es
  | _, [], _ => by simp [compFieldHOL, expressionsCost, expressionCost]
  | idx, _ :: shs, es => by
    unfold compFieldHOL
    split
    · exact expressionsCost_take _ _
    · exact Nat.le_trans (compFieldHOL_cost (idx - 1) shs _) (expressionsCost_drop _ _)

theorem loadShapeBytesHOLW_zero_of_zero {width : Nat} [NeZero width]
    (v : CrepExpHOL width) (hv : expressionCost v = 0) :
    ∀ (cnt : Nat) (addr : BitVec width),
      expressionsCost (loadShapeBytesHOLW addr cnt v) = 0
  | 0, _ => by simp [loadShapeBytesHOLW, expressionsCost]
  | cnt + 1, addr => by
    simp only [loadShapeBytesHOLW, expressionsCost, loadShapeBytesHOLW_zero_of_zero v hv cnt]
    split <;> simp [expressionCost, expressionsCost, hv]

theorem loadShapeBytesHOLW_le_one {width : Nat} [NeZero width]
    (v : CrepExpHOL width) :
    ∀ (cnt : Nat), cnt ≤ 1 →
      expressionsCost (loadShapeBytesHOLW (0 : BitVec width) cnt v) ≤ expressionCost v
  | 0, _ => by simp [loadShapeBytesHOLW, expressionsCost]
  | 1, _ => by
    simp [loadShapeBytesHOLW, expressionsCost, expressionCost]
  | _ + 2, h => by omega

theorem cexpHeads_cost {width : Nat} [NeZero width] :
    ∀ (xss : List (List (CrepExpHOL width))) (hs : List (CrepExpHOL width)),
      cexpHeads xss = some hs →
      expressionsCost hs ≤ (xss.map expressionsCost).sum
  | [], _, h => by injection h with h'; subst h'; simp [expressionsCost]
  | xs :: xss, hs, h => by
    unfold cexpHeads at h
    cases xs with
    | nil => cases h
    | cons x xs' =>
      cases hh : cexpHeads xss with
      | none => rw [hh] at h; cases h
      | some rest =>
        rw [hh] at h; injection h with h'; subst h'
        simp only [expressionsCost, List.map_cons, List.sum_cons]
        have ih := cexpHeads_cost xss rest hh
        omega

theorem vars_map_zero {width : Nat} [NeZero width] :
    ∀ ns : List Nat, expressionsCost (ns.map (CrepExpHOL.var (width := width))) = 0
  | [] => rfl
  | _ :: ns => by simp [expressionsCost, expressionCost, vars_map_zero (width := width) ns]

theorem replicate_const_zero {width : Nat} [NeZero width] :
    ∀ n : Nat, expressionsCost (List.replicate n (CrepExpHOL.const (0 : BitVec width))) = 0
  | 0 => rfl
  | n + 1 => by
    have ih := replicate_const_zero (width := width) n
    rw [List.replicate_succ]
    simpa [expressionsCost, expressionCost] using ih

theorem crepExp_cost_le {width contextWidth : Nat} [NeZero width] [NeZero contextWidth]
    (ctx : PanToCrepContextExact contextWidth) :
    (∀ e : ExpHOL width, loadSafeExp e = true →
      expressionsCost (InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e).1 ≤ panExpCost e) ∧
    (∀ es : List (ExpHOL width), loadSafeExps es = true →
      expressionsCost ((InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList ctx es).flatMap Prod.fst) ≤ panExpsCost es ∧
      ((InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList ctx es |>.map Prod.fst).map expressionsCost).sum ≤ panExpsCost es) := by
  have he : ∀ e : ExpHOL width, loadSafeExp e = true →
      expressionsCost (InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e).1 ≤ panExpCost e := by
    intro e
    induction e using (measure (sizeOf : ExpHOL width → Nat)).wf.induction with
    | h e ih =>
      change ∀ c, sizeOf c < sizeOf e → loadSafeExp c = true →
        expressionsCost (InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx c).1 ≤ panExpCost c at ih
      have ihm : ∀ es : List (ExpHOL width), (∀ x ∈ es, sizeOf x < sizeOf e) → loadSafeExps es = true →
          expressionsCost ((InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList ctx es).flatMap Prod.fst) ≤ panExpsCost es ∧
          ((InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList ctx es |>.map Prod.fst).map expressionsCost).sum ≤ panExpsCost es := by
        intro es hes hls
        induction es with
        | nil => simp [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList, expressionsCost, panExpsCost]
        | cons x xs ihxs =>
          simp only [loadSafeExps, Bool.and_eq_true_iff] at hls
          have ihx := ih x (hes x List.mem_cons_self) hls.1
          have ihrest := ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy)) hls.2
          simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList,
            List.flatMap_cons, expressionsCost_append, List.map_cons, List.sum_cons, panExpsCost]
          exact ⟨Nat.add_le_add ihx ihrest.1, Nat.add_le_add ihx ihrest.2⟩
      intro hls
      cases e with
      | const _ | baseAddr | topAddr | bytesInWord | nstruct _ _ | nfield _ _ =>
        simp [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, expressionsCost, expressionCost, panExpCost]
      | var vk vn =>
        cases vk with
        | global => simp [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, expressionsCost, expressionCost, panExpCost]
        | «local» =>
          simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
          cases ctx.vars.lookup vn with
          | none => simp [expressionsCost, expressionCost]
          | some p => simp [vars_map_zero]
      | rstruct es =>
        simp only [loadSafeExp] at hls
        have h := ihm es (by intros; sizeOf_list_dec) hls
        simpa [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost] using h.1
      | rfield idx child =>
        simp only [loadSafeExp] at hls
        have hc := ih child (by decreasing_trivial) hls
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
        cases hsh : (InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx child).2 with
        | comb shs => exact Nat.le_trans (compFieldHOL_cost idx shs _) hc
        | one | named _ => simp [expressionsCost, expressionCost]
      | load sh child =>
        simp only [loadSafeExp, Bool.and_eq_true_iff, Bool.or_eq_true, decide_eq_true_eq] at hls
        have hc := ih child (by decreasing_trivial) hls.2
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
        rcases hcomp : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx child with ⟨vals, csh⟩
        rw [hcomp] at hc
        cases vals with
        | nil => simp [expressionsCost, expressionCost]
        | cons addr rest =>
          simp only [expressionsCost] at hc
          rcases hls.1 with hle1 | hzero
          · exact Nat.le_trans (loadShapeBytesHOLW_le_one addr _ hle1) (by omega)
          · have haddr0 : expressionCost addr = 0 := by omega
            simp [loadShapeBytesHOLW_zero_of_zero addr haddr0]
      | load32 child | loadByte child =>
        simp only [loadSafeExp] at hls
        have hc := ih child (by decreasing_trivial) hls
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
        rcases hcomp : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx child with ⟨vals, csh⟩
        rw [hcomp] at hc
        cases vals with
        | nil => simp [expressionsCost, expressionCost]
        | cons addr rest =>
          cases csh with
          | one => simp only [expressionsCost, expressionCost] at hc ⊢; omega
          | comb _ | named _ => simp [expressionsCost, expressionCost]
      | op op es =>
        simp only [loadSafeExp] at hls
        have h := ihm es (by intros; sizeOf_list_dec) hls
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
        cases hh : cexpHeads (InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList ctx es |>.map Prod.fst) with
        | none => simp [expressionsCost, expressionCost]
        | some hs =>
          have hch := cexpHeads_cost _ hs hh
          simp only [expressionsCost, expressionCost, Nat.add_zero]
          exact Nat.le_trans hch h.2
      | panop op es =>
        simp only [loadSafeExp] at hls
        have h := ihm es (by intros; sizeOf_list_dec) hls
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
        cases hh : cexpHeads (InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList ctx es |>.map Prod.fst) with
        | none => simp [expressionsCost, expressionCost]
        | some hs =>
          have hch := cexpHeads_cost _ hs hh
          simp only [expressionsCost, expressionCost, Nat.add_zero]
          exact Nat.le_trans hch h.2
      | cmp op l r =>
        simp only [loadSafeExp, Bool.and_eq_true_iff] at hls
        have hl := ih l (by decreasing_trivial) hls.1
        have hr := ih r (by decreasing_trivial) hls.2
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
        rcases hcl : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx l with ⟨vl, sl⟩
        rcases hcr : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx r with ⟨vr, sr⟩
        rw [hcl] at hl; rw [hcr] at hr
        cases vl with
        | nil => simp [expressionsCost, expressionCost]
        | cons al _ =>
          cases vr with
          | nil => simp [expressionsCost, expressionCost]
          | cons ar _ =>
            simp only [expressionsCost, expressionCost] at hl hr ⊢
            omega
      | shift op l r =>
        simp only [loadSafeExp, Bool.and_eq_true_iff] at hls
        have hl := ih l (by decreasing_trivial) hls.1
        have hr := ih r (by decreasing_trivial) hls.2
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW, panExpCost]
        rcases hcl : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx l with ⟨vl, sl⟩
        rcases hcr : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx r with ⟨vr, sr⟩
        rw [hcl] at hl; rw [hcr] at hr
        cases vl with
        | nil => simp [expressionsCost, expressionCost]
        | cons al _ =>
          cases vr with
          | nil => simp [expressionsCost, expressionCost]
          | cons ar _ =>
            simp only [expressionsCost, expressionCost] at hl hr ⊢
            omega
  refine ⟨he, fun es hls => ?_⟩
  induction es with
  | nil => simp [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList, expressionsCost, panExpsCost]
  | cons x xs ih =>
    simp only [loadSafeExps, Bool.and_eq_true_iff] at hls
    have hx := he x hls.1
    have hxs := ih hls.2
    simp only [InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList,
      List.flatMap_cons, expressionsCost_append, List.map_cons, List.sum_cons, panExpsCost]
    exact ⟨Nat.add_le_add hx hxs.1, Nat.add_le_add hx hxs.2⟩

theorem nestedDecsHOL_cost {width : Nat} [NeZero width] :
    ∀ (names : List Nat) (vals : List (CrepExpHOL width)) (body : CrepProgHOL width),
      programCost (nestedDecsHOL names vals body) ≤ expressionsCost vals + programCost body
  | [], [], _ => by simp [nestedDecsHOL, expressionsCost]
  | [], _ :: _, _ => by simp [nestedDecsHOL, programCost]
  | _ :: _, [], _ => by simp [nestedDecsHOL, programCost]
  | n :: ns, v :: vs, body => by
    simp only [nestedDecsHOL, programCost, expressionsCost]
    have ih := nestedDecsHOL_cost ns vs body
    omega

theorem crepNestedSeqHOL_cost {width : Nat} [NeZero width] :
    ∀ ps : List (CrepProgHOL width),
      programCost (crepNestedSeqHOL ps) = (ps.map programCost).sum
  | [] => by simp [crepNestedSeqHOL, programCost]
  | p :: ps => by simp [crepNestedSeqHOL, programCost, crepNestedSeqHOL_cost ps]

theorem zipWith_assign_cost {width : Nat} [NeZero width] :
    ∀ (ns : List Nat) (es : List (CrepExpHOL width)),
      ((List.zipWith (CrepProgHOL.assign (width := width)) ns es).map programCost).sum ≤ expressionsCost es
  | [], _ => by simp
  | _ :: _, [] => by simp [expressionsCost]
  | _ :: ns, e :: es => by
    simp only [List.zipWith_cons_cons, List.map_cons, List.sum_cons, programCost, expressionsCost]
    exact Nat.add_le_add_left (zipWith_assign_cost ns es) _

theorem zipWith_assign_vars_zero {width : Nat} [NeZero width] (ns ts : List Nat) :
    programCost (crepNestedSeqHOL (List.zipWith (CrepProgHOL.assign (width := width)) ns (ts.map CrepExpHOL.var))) = 0 := by
  rw [crepNestedSeqHOL_cost]
  have h := zipWith_assign_cost (width := width) ns (ts.map CrepExpHOL.var)
  rw [vars_map_zero] at h
  omega

theorem storesHOL_vars_zero {width : Nat} [NeZero width] (addrName : Nat) :
    ∀ (ts : List Nat) (off : BitVec width),
      programCost (crepNestedSeqHOL (storesHOL (.var addrName) (ts.map CrepExpHOL.var) off)) = 0
  | [], _ => by simp [storesHOL, crepNestedSeqHOL, programCost]
  | _ :: ts, off => by
    simp only [List.map_cons, storesHOL, crepNestedSeqHOL, programCost, storesHOL_vars_zero addrName ts]
    split <;> simp [expressionCost, expressionsCost]

theorem storeGlobalsHOL_vars_zero {width : Nat} [NeZero width] :
    ∀ (ts : List Nat) (addr : BitVec 5),
      programCost (crepNestedSeqHOL (storeGlobalsHOL addr (ts.map (CrepExpHOL.var (width := width))))) = 0
  | [], _ => by simp [storeGlobalsHOL, crepNestedSeqHOL, programCost]
  | _ :: ts, addr => by
    simp [storeGlobalsHOL, crepNestedSeqHOL, programCost, expressionCost, storeGlobalsHOL_vars_zero ts]

theorem loadGlobalsHOL_zero {width : Nat} [NeZero width] :
    ∀ (cnt : Nat) (addr : BitVec 5),
      expressionsCost (loadGlobalsHOL (width := width) addr cnt) = 0
  | 0, _ => rfl
  | cnt + 1, addr => by
    simp [loadGlobalsHOL, expressionsCost, expressionCost, loadGlobalsHOL_zero cnt]

theorem panMap2_assign_loadGlobals_zero {width : Nat} [NeZero width] :
    ∀ (ns : List Nat) (es : List (CrepExpHOL width)),
      expressionsCost es = 0 →
      programCost (crepNestedSeqHOL (panMap2 (fun d s => CrepProgHOL.assign (width := width) d s) ns es)) = 0
  | [], _, _ => by simp [panMap2, crepNestedSeqHOL, programCost]
  | _ :: _, [], _ => by simp [panMap2, crepNestedSeqHOL, programCost]
  | _ :: ns, e :: es, h => by
    simp only [expressionsCost] at h
    have he : expressionCost e = 0 := by omega
    have hes : expressionsCost es = 0 := by omega
    simp [panMap2, crepNestedSeqHOL, programCost, he, panMap2_assign_loadGlobals_zero ns es hes]

theorem expHdlExact_zero {width : Nat} [NeZero width]
    (fm : HolFiniteMapExact MlS (ShapeHOL × List Nat)) (v : MlS) :
    programCost (expHdlExact (width := width) fm v) = 0 := by
  unfold expHdlExact
  cases fm.lookup v with
  | none => simp [programCost]
  | some p => exact panMap2_assign_loadGlobals_zero p.2 _ (loadGlobalsHOL_zero _ _)

theorem crepProg_cost_le {width : Nat} [NeZero width] :
    ∀ (p : ProgHOL width) (ctx : PanToCrepContextExact width),
      loadSafeProg p = true →
      programCost (InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW ctx p) ≤ panProgCost p := by
  intro p
  induction p using (measure (sizeOf : ProgHOL width → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p → ∀ ctx, loadSafeProg q = true →
      programCost (InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW ctx q) ≤ panProgCost q at ih
    intro ctx hls
    cases p with
    | skip | «break» | «continue» | tick | annot _ _ =>
      simp [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW, programCost, panProgCost]
    | assign vk name e =>
      cases vk with
      | global =>
        simp [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
          InitECandidate.Proofs.CrepKernelComputation.compileGlobalAssignExactHOLW, programCost]
      | «local» =>
        simp only [loadSafeProg] at hls
        have he := (crepExp_cost_le ctx).1 e hls
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
          InitECandidate.Proofs.CrepKernelComputation.compileLocalAssignExactHOLW, panProgCost]
        rcases hce : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e with ⟨expressions, esh⟩
        rw [hce] at he
        dsimp only at he ⊢
        cases hlookup : ctx.vars.lookup name with
        | none => simp [programCost]
        | some p =>
          rcases p with ⟨vsh, names⟩
          dsimp only
          split
          · simp [programCost]
          · split
            · rw [crepNestedSeqHOL_cost]
              exact Nat.le_trans (zipWith_assign_cost _ _) he
            · have hnd := nestedDecsHOL_cost ((List.range names.length).map (fun i => ctx.vmax + i + 1))
                expressions
                (crepNestedSeqHOL (List.zipWith CrepProgHOL.assign names
                  (((List.range names.length).map (fun i => ctx.vmax + i + 1)).map CrepExpHOL.var)))
              rw [zipWith_assign_vars_zero, Nat.add_zero] at hnd
              exact Nat.le_trans hnd he
    | primitive name op args =>
      simp only [loadSafeProg] at hls
      have ha := ((crepExp_cost_le ctx).2 args hls).1
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compilePrimitiveExactHOLW, panProgCost]
      cases hlookup : ctx.vars.lookup name with
      | none => simp [programCost]
      | some p =>
        rcases p with ⟨vsh, names⟩
        dsimp only
        let vals := (InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLWList ctx args).flatMap Prod.fst
        let temps := (List.range vals.length).map (fun index => ctx.vmax + index + 1)
        have hnd := nestedDecsHOL_cost (width := width) temps vals (.primitive names op temps)
        simp only [programCost, Nat.add_zero] at hnd
        exact Nat.le_trans hnd ha
    | store addr val =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have ha := (crepExp_cost_le ctx).1 addr hls.1
      have hv := (crepExp_cost_le ctx).1 val hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileStoreExactHOLW, panProgCost]
      rcases hca : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx addr with ⟨va, sa⟩
      rcases hcv : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx val with ⟨vv, sv⟩
      rw [hca] at ha; rw [hcv] at hv
      dsimp only at ha hv ⊢
      cases va with
      | nil => simp [programCost]
      | cons ca _ =>
        dsimp only
        split
        · simp [programCost]
        · have hnd := nestedDecsHOL_cost
            ((ctx.vmax + 1) :: (List.range (sizeOfShapeHOL sv)).map (fun i => ctx.vmax + 1 + i + 1))
            (ca :: vv)
            (crepNestedSeqHOL (storesHOL (.var (ctx.vmax + 1))
              (((List.range (sizeOfShapeHOL sv)).map (fun i => ctx.vmax + 1 + i + 1)).map CrepExpHOL.var) 0))
          rw [storesHOL_vars_zero, Nat.add_zero] at hnd
          simp only [expressionsCost] at ha hnd
          omega
    | store32 addr val =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have ha := (crepExp_cost_le ctx).1 addr hls.1
      have hv := (crepExp_cost_le ctx).1 val hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileStore32ExactHOLW, panProgCost]
      rcases hca : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx addr with ⟨va, _⟩
      rcases hcv : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx val with ⟨vv, _⟩
      rw [hca] at ha; rw [hcv] at hv
      cases va with
      | nil => simp [programCost]
      | cons ca _ =>
        cases vv with
        | nil => simp [programCost]
        | cons cv _ => simp only [expressionsCost, programCost] at ha hv ⊢; omega
    | storeByte addr val =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have ha := (crepExp_cost_le ctx).1 addr hls.1
      have hv := (crepExp_cost_le ctx).1 val hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileStoreByteExactHOLW, panProgCost]
      rcases hca : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx addr with ⟨va, _⟩
      rcases hcv : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx val with ⟨vv, _⟩
      rw [hca] at ha; rw [hcv] at hv
      cases va with
      | nil => simp [programCost]
      | cons ca _ =>
        cases vv with
        | nil => simp [programCost]
        | cons cv _ => simp only [expressionsCost, programCost] at ha hv ⊢; omega
    | «return» e =>
      simp only [loadSafeProg] at hls
      have he := (crepExp_cost_le ctx).1 e hls
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileReturnExactHOLW, panProgCost]
      rcases hce : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e with ⟨vals, sh⟩
      rw [hce] at he
      dsimp only at he ⊢
      split
      · simp [programCost, expressionsCost]
      · simpa [programCost] using he
    | raise exn e =>
      simp only [loadSafeProg] at hls
      have he := (crepExp_cost_le ctx).1 e hls
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileRaiseExactHOLW, panProgCost]
      cases hlookup : ctx.eids.lookup exn with
      | none => simp [programCost]
      | some code =>
        rcases hce : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e with ⟨vals, sh⟩
        rw [hce] at he
        dsimp only at he ⊢
        split
        · simp [programCost]
        · simp only [programCost, Nat.add_zero]
          have hnd := nestedDecsHOL_cost (width := width)
            ((List.range (sizeOfShapeHOL sh)).map (fun i => ctx.vmax + i + 1))
            vals
            (crepNestedSeqHOL (storeGlobalsHOL 0 (((List.range (sizeOfShapeHOL sh)).map (fun i => ctx.vmax + i + 1)).map CrepExpHOL.var)))
          rw [storeGlobalsHOL_vars_zero, Nat.add_zero] at hnd
          exact Nat.le_trans hnd he
    | shMemLoad op vk name addr =>
      cases vk with
      | global =>
        simp [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
          InitECandidate.Proofs.CrepKernelComputation.compileGlobalShMemLoadExactHOLW, programCost]
      | «local» =>
        simp only [loadSafeProg] at hls
        have ha := (crepExp_cost_le ctx).1 addr hls
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
          InitECandidate.Proofs.CrepKernelComputation.compileShMemLoadExactHOLW, panProgCost]
        rcases hca : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx addr with ⟨va, _⟩
        rw [hca] at ha
        cases va with
        | nil => simp [programCost]
        | cons ca _ =>
          dsimp only
          cases hlookup : ctx.vars.lookup name with
          | none => simp [programCost]
          | some p =>
            rcases p with ⟨_, dsts⟩
            cases dsts with
            | nil => simp [programCost]
            | cons dst _ => simp only [expressionsCost, programCost] at ha ⊢; omega
    | shMemStore op val addr =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have hv := (crepExp_cost_le ctx).1 val hls.1
      have ha := (crepExp_cost_le ctx).1 addr hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileShMemStoreExactHOLW, panProgCost]
      rcases hcv : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx val with ⟨vv, _⟩
      rcases hca : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx addr with ⟨va, _⟩
      rw [hcv] at hv; rw [hca] at ha
      cases vv with
      | nil => simp [programCost]
      | cons cv _ =>
        cases va with
        | nil => simp [programCost]
        | cons ca _ => simp only [expressionsCost, programCost] at hv ha ⊢; omega
    | extCall fn e1 e2 e3 e4 =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have h1 := (crepExp_cost_le ctx).1 e1 hls.1.1.1
      have h2 := (crepExp_cost_le ctx).1 e2 hls.1.1.2
      have h3 := (crepExp_cost_le ctx).1 e3 hls.1.2
      have h4 := (crepExp_cost_le ctx).1 e4 hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileExtCallExactHOLW, panProgCost]
      rcases hc1 : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e1 with ⟨v1, s1⟩
      rcases hc2 : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e2 with ⟨v2, s2⟩
      rcases hc3 : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e3 with ⟨v3, s3⟩
      rcases hc4 : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e4 with ⟨v4, s4⟩
      rw [hc1] at h1; rw [hc2] at h2; rw [hc3] at h3; rw [hc4] at h4
      dsimp only
      split
      · simp only [expressionsCost, programCost] at h1 h2 h3 h4 ⊢; omega
      · simp [programCost]
    | dec name sh e body =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have he := (crepExp_cost_le ctx).1 e hls.1
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileDecExactHOLW, panProgCost]
      rcases hce : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx e with ⟨values, csh⟩
      rw [hce] at he
      dsimp only at he ⊢
      split
      · simp [programCost]
      · have ihb := ih body (by decreasing_trivial)
          { ctx with
            vars := ctx.vars.update (name, (csh, (List.range (sizeOfShapeHOL csh)).map (fun index => ctx.vmax + index + 1)))
            vmax := ctx.vmax + sizeOfShapeHOL csh }
          hls.2
        refine Nat.le_trans (nestedDecsHOL_cost _ _ _) ?_
        omega
    | decCall name sh fn args body =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have ha := ((crepExp_cost_le ctx).2 args hls.1).1
      have ihb := ih body (by decreasing_trivial)
        { ctx with
          vars := ctx.vars.update (name, (sh, (List.range (sizeOfShapeHOL sh)).map (fun index => ctx.vmax + index + 1)))
          vmax := ctx.vmax + sizeOfShapeHOL sh }
        hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileDecCallExactHOLW, panProgCost]
      refine Nat.le_trans (nestedDecsHOL_cost _ _ _) ?_
      rw [replicate_const_zero, Nat.zero_add]
      simp only [programCost, programCost_call]
      omega
    | seq a b =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have iha := ih a (by decreasing_trivial) ctx hls.1
      have ihb := ih b (by decreasing_trivial) ctx hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW, programCost, panProgCost]
      omega
    | ite c a b =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have hc := (crepExp_cost_le ctx).1 c hls.1.1
      have iha := ih a (by decreasing_trivial) ctx hls.1.2
      have ihb := ih b (by decreasing_trivial) ctx hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileIfExactHOLW, panProgCost]
      rcases hcc : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx c with ⟨vc, _⟩
      rw [hcc] at hc
      cases vc with
      | nil => simp [programCost]
      | cons cc _ => simp only [expressionsCost, programCost] at hc ⊢; omega
    | «while» c body =>
      simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
      have hc := (crepExp_cost_le ctx).1 c hls.1
      have ihb := ih body (by decreasing_trivial) ctx hls.2
      simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
        InitECandidate.Proofs.CrepKernelComputation.compileWhileExactHOLW, panProgCost]
      rcases hcc : InitECandidate.Proofs.CrepKernelComputation.compileExpExactHOLW ctx c with ⟨vc, _⟩
      rw [hcc] at hc
      cases vc with
      | nil => simp [programCost]
      | cons cc _ => simp only [expressionsCost, programCost] at hc ⊢; omega
    | call info fn args =>
      cases info with
      | none =>
        simp only [loadSafeProg] at hls
        have ha := ((crepExp_cost_le ctx).2 args hls).1
        simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
          InitECandidate.Proofs.CrepKernelComputation.compileCallNoReturnExactHOLW, programCost_call, panProgCost]
        omega
      | some inf =>
        rcases inf with ⟨rk, hdl⟩
        cases rk with
        | none =>
          cases hdl with
          | none =>
            simp only [loadSafeProg] at hls
            have ha := ((crepExp_cost_le ctx).2 args hls).1
            simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW,
              InitECandidate.Proofs.CrepKernelComputation.compileCallResultNoHandlerExactHOLW, panProgCost]
            refine Nat.le_trans (nestedDecsHOL_cost _ _ _) ?_
            rw [replicate_const_zero, Nat.zero_add]
            simp only [programCost_call]
            omega
          | some hb =>
            rcases hb with ⟨exn, evar, body⟩
            simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
            have ha := ((crepExp_cost_le ctx).2 args hls.1).1
            simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW, panProgCost]
            split
            · simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallHandlerMissingEidExactHOLW,
                InitECandidate.Proofs.CrepKernelComputation.compileCallResultNoHandlerExactHOLW]
              refine Nat.le_trans (nestedDecsHOL_cost _ _ _) ?_
              rw [replicate_const_zero, Nat.zero_add]
              simp only [programCost_call]
              omega
            · rename_i exceptionCode _
              simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallHandlerPresentEidExactHOLW]
              have ihb := ih body (by simp_wf; omega) ctx hls.2
              refine Nat.le_trans (nestedDecsHOL_cost _ _ _) ?_
              rw [replicate_const_zero, Nat.zero_add]
              simp only [programCost_call, programCost, expHdlExact_zero, Nat.zero_add]
              omega
        | some rkv =>
          rcases rkv with ⟨vk, rname⟩
          cases hdl with
          | none =>
            simp only [loadSafeProg] at hls
            have ha := ((crepExp_cost_le ctx).2 args hls).1
            simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW, panProgCost]
            split
            · simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultFallbackNoHandlerExactHOLW, programCost_call]
              omega
            · simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultNoHandlerExactHOLW, programCost_call]
              omega
          | some hb =>
            rcases hb with ⟨exn, evar, body⟩
            simp only [loadSafeProg, Bool.and_eq_true_iff] at hls
            have ha := ((crepExp_cost_le ctx).2 args hls.1).1
            have ihb := ih body (by simp_wf; omega) ctx hls.2
            simp only [InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW, panProgCost]
            split
            · split
              · simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultFallbackHandlerMissingEidExactHOLW,
                  InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultFallbackNoHandlerExactHOLW, programCost_call]
                omega
              · simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultFallbackHandlerPresentEidExactHOLW,
                  programCost_call, programCost, expHdlExact_zero, Nat.zero_add]
                omega
            · split
              · simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultHandlerMissingEidExactHOLW,
                  InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultNoHandlerExactHOLW, programCost_call]
                omega
              · simp only [InitECandidate.Proofs.CrepKernelComputation.compileCallWrappedResultHandlerPresentEidExactHOLW,
                  programCost_call, programCost, expHdlExact_zero, Nat.zero_add]
                omega

theorem filter_inlinableHOL_nil {width : Nat} [NeZero width] :
    ∀ decls : List (DeclHOL width),
      decls.all fnPostGlobalsGood = true →
      decls.filter inlinableHOL = []
  | [], _ => rfl
  | d :: ds, h => by
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    cases d with
    | function fn =>
      simp only [fnPostGlobalsGood, Bool.and_eq_true_iff, Bool.not_eq_true'] at h
      simp [inlinableHOL, h.1.1.1, filter_inlinableHOL_nil ds h.2]
    | exnDecl _ _ =>
      simp [inlinableHOL, filter_inlinableHOL_nil ds h.2]
    | decl _ _ _ => simp [fnPostGlobalsGood] at h
    | name _ _ => simp [fnPostGlobalsGood] at h

theorem functionsHOL_good {width : Nat} [NeZero width] :
    ∀ decls : List (DeclHOL width),
      decls.all fnPostGlobalsGood = true →
      ∀ entry ∈ functionsHOL decls,
        loadSafeProg entry.2.2.1 = true ∧ panProgCost entry.2.2.1 ≤ 448
  | [], _, _, hmem => by simp [functionsHOL] at hmem
  | d :: ds, h, entry, hmem => by
    simp only [List.all_cons, Bool.and_eq_true_iff] at h
    cases d with
    | function fn =>
      simp only [functionsHOL, List.mem_cons] at hmem
      rcases hmem with rfl | htail
      · simp only [fnPostGlobalsGood, Bool.and_eq_true_iff, decide_eq_true_eq] at h
        exact ⟨h.1.1.2, h.1.2⟩
      · exact functionsHOL_good ds h.2 entry htail
    | exnDecl _ _ =>
      simp only [functionsHOL] at hmem
      exact functionsHOL_good ds h.2 entry hmem
    | decl _ _ _ => simp [fnPostGlobalsGood] at h
    | name _ _ => simp [fnPostGlobalsGood] at h

theorem foldr_max_le_bound :
    ∀ (xs : List Nat) (bound : Nat),
      3 ≤ bound → (∀ x ∈ xs, x ≤ bound) → xs.foldr max 3 ≤ bound
  | [], _, hb, _ => hb
  | x :: xs, bound, hb, hall => by
    simp only [List.foldr_cons]
    exact Nat.max_le.mpr ⟨hall x List.mem_cons_self,
      foldr_max_le_bound xs bound hb (fun y hy => hall y (List.mem_cons_of_mem _ hy))⟩

theorem listBudget_compileProgDeclsHOLW_le_448 {width : Nat} [NeZero width]
    (decls : List (DeclHOL width)) (h : decls.all fnPostGlobalsGood = true) :
    listBudget (compileProgDeclsHOLW decls) ≤ 448 := by
  unfold compileProgDeclsHOLW
  have hnil : decls.filter inlinableHOL = [] := filter_inlinableHOL_nil decls h
  rw [hnil]
  have hinl : CrepInlineCanonical.compileInlTopHOLExact
      ((functionsHOL ([] : List (DeclHOL width))).map Prod.fst)
      (compileToCrepExactHOLW decls) = compileToCrepExactHOLW decls := by
    have hfn : (functionsHOL ([] : List (DeclHOL width))).map Prod.fst = [] := rfl
    rw [hfn]
    unfold CrepInlineCanonical.compileInlTopHOLExact
    have hflt : (compileToCrepExactHOLW decls).filter (fun triple => ([] : List MlS).contains triple.1) = [] := by
      simp
    rw [hflt]
    exact compileInlProg_emptyLookup
      (CrepInlineCanonical.alistToFmapHOLExact []) []
      (CrepInlineCanonical.supportKeys_alistToFmapHOLExact [])
      (fun _ => rfl)
      (compileToCrepExactHOLW decls)
  rw [hinl]
  unfold listBudget compileToCrepExactHOLW
  apply foldr_max_le_bound _ 448 (by omega)
  intro x hx
  rcases List.mem_map.mp hx with ⟨triple, htr, rfl⟩
  rcases List.mem_map.mp htr with ⟨entry, hentry, rfl⟩
  dsimp only
  have hent := functionsHOL_good decls h entry hentry
  have hsimp := progCost_simp (compFuncExactHOLW (makeFuncsExactHOL (functionsHOL decls))
    (getEidsFromDeclsHOL decls) entry.2.1 entry.2.2.1)
  have hcf : compFuncExactHOLW (makeFuncsExactHOL (functionsHOL decls))
      (getEidsFromDeclsHOL decls) entry.2.1 entry.2.2.1 =
      InitECandidate.Proofs.CrepKernelComputation.compileProgExactHOLW
        (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
          (makeFuncsExactHOL (functionsHOL decls))
          (sizeOfShapeHOL (ShapeHOL.comb (entry.2.1.map Prod.snd)) - 1)
          (getEidsFromDeclsHOL decls))
        entry.2.2.1 := by
    rw [InitECandidate.Proofs.CrepKernelComputation.compFunc_function_eq]
    rfl
  rw [hcf] at hsimp ⊢
  have hcrep := crepProg_cost_le entry.2.2.1
    (mkCtxtExactHOL (panToCrepMakeVmapHOLExact entry.2.1)
      (makeFuncsExactHOL (functionsHOL decls))
      (sizeOfShapeHOL (ShapeHOL.comb (entry.2.1.map Prod.snd)) - 1)
      (getEidsFromDeclsHOL decls))
    hent.1
  omega

/-! ## 6. Structural Source Codec Equivalence and `guestAst` Evaluation -/

mutual
  def sizeOfShapeS : Shape → Nat
    | .one => 1
    | .comb shapes => sizeOfShapesS shapes
    | .named _ => 1
  termination_by structural shape => shape

  def sizeOfShapesS : List Shape → Nat
    | [] => 0
    | s :: ss => sizeOfShapeS s + sizeOfShapesS ss
  termination_by structural ss => ss
end

theorem sizeOfShapeS_eq :
    (∀ s : Shape, sizeOfShapeHOL (InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural s) = sizeOfShapeS s) ∧
    (∀ ss : List Shape, sizeOfShapesHOL (InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural ss) = sizeOfShapesS ss) := by
  have hs : ∀ s : Shape, sizeOfShapeHOL (InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural s) = sizeOfShapeS s := by
    intro s
    induction s using (measure (sizeOf : Shape → Nat)).wf.induction with
    | h s ih =>
      have ihm : ∀ ss : List Shape, (∀ x ∈ ss, sizeOf x < sizeOf s) →
          sizeOfShapesHOL (InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural ss) = sizeOfShapesS ss := by
        intro ss hss
        induction ss with
        | nil => rfl
        | cons x xs ihxs =>
          simp only [InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,
            sizeOfShapesHOL, sizeOfShapesS,
            ih x (hss x List.mem_cons_self), ihxs (fun y hy => hss y (List.mem_cons_of_mem _ hy))]
      cases s with
      | one => rfl
      | named _ => rfl
      | comb ss =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural, sizeOfShapeHOL, sizeOfShapeS]
        exact ihm ss (by intro x hx; have := List.sizeOf_lt_of_mem hx; simp only [Shape.comb.sizeOf_spec]; omega)
  refine ⟨hs, fun ss => ?_⟩
  induction ss with
  | nil => rfl
  | cons x xs ih =>
    simp only [InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,
      sizeOfShapesHOL, sizeOfShapesS, hs x, ih]

mutual
  def shapeFreeS : Shape → Bool
    | .one => true
    | .comb shapes => shapesFreeS shapes
    | .named _ => false
  termination_by structural shape => shape

  def shapesFreeS : List Shape → Bool
    | [] => true
    | s :: ss => shapeFreeS s && shapesFreeS ss
  termination_by structural ss => ss
end

theorem shapeFreeS_eq :
    (∀ s : Shape, shapeFree (InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural s) = shapeFreeS s) ∧
    (∀ ss : List Shape, shapesFree (InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural ss) = shapesFreeS ss) := by
  have hs : ∀ s : Shape, shapeFree (InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural s) = shapeFreeS s := by
    intro s
    induction s using (measure (sizeOf : Shape → Nat)).wf.induction with
    | h s ih =>
      have ihm : ∀ ss : List Shape, (∀ x ∈ ss, sizeOf x < sizeOf s) →
          shapesFree (InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural ss) = shapesFreeS ss := by
        intro ss hss
        induction ss with
        | nil => rfl
        | cons x xs ihxs =>
          simp only [InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,
            shapesFree, shapesFreeS,
            ih x (hss x List.mem_cons_self), ihxs (fun y hy => hss y (List.mem_cons_of_mem _ hy))]
      cases s with
      | one => rfl
      | named _ => rfl
      | comb ss =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.shapeToHOLStructural, shapeFree, shapeFreeS]
        exact ihm ss (by intro x hx; have := List.sizeOf_lt_of_mem hx; simp only [Shape.comb.sizeOf_spec]; omega)
  refine ⟨hs, fun ss => ?_⟩
  induction ss with
  | nil => rfl
  | cons x xs ih =>
    simp only [InitECandidate.Proofs.FrontendCodecComputation.shapeListToHOLStructural,
      shapesFree, shapesFreeS, hs x, ih]

mutual
  def panExpCostS {width : Nat} : (e : Exp (BitVec width)) → Nat
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => 0
    | .rStruct es | .op _ es | .panOp _ es => panExpsCostS es
    | .rField _ e | .load _ e | .load32 e | .loadByte e | .nField _ e => panExpCostS e
    | .nStruct _ fs => panNamedExpsCostS fs
    | .cmp _ a b => panExpCostS a + panExpCostS b + 1
    | .shift _ a b => panExpCostS a + panExpCostS b
  termination_by structural e => e

  def panExpsCostS {width : Nat} : (es : List (Exp (BitVec width))) → Nat
    | [] => 0
    | e :: es => panExpCostS e + panExpsCostS es
  termination_by structural es => es

  def panNamedExpsCostS {width : Nat} : (fs : List (String × Exp (BitVec width))) → Nat
    | [] => 0
    | (_, e) :: fs => panExpCostS e + panNamedExpsCostS fs
  termination_by structural fs => fs
end

theorem panExpCostS_eq {width : Nat} [NeZero width] :
    (∀ e : Exp (BitVec width), panExpCost (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural e) = panExpCostS e) ∧
    (∀ es : List (Exp (BitVec width)), panExpsCost (es.map InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural) = panExpsCostS es) := by
  have he : ∀ e : Exp (BitVec width), panExpCost (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural e) = panExpCostS e := by
    intro e
    induction e using (measure (sizeOf : Exp (BitVec width) → Nat)).wf.induction with
    | h e ih =>
      change ∀ c, sizeOf c < sizeOf e → panExpCost (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural c) = panExpCostS c at ih
      have ihm : ∀ es : List (Exp (BitVec width)), (∀ x ∈ es, sizeOf x < sizeOf e) →
          panExpsCost (InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural es) = panExpsCostS es := by
        intro es hes
        induction es with
        | nil => rfl
        | cons x xs ihxs =>
          simp only [InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
            panExpsCost, panExpsCostS, ih x (hes x List.mem_cons_self),
            ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy))]
      have ihn : ∀ fs : List (String × Exp (BitVec width)), (∀ p ∈ fs, sizeOf p.2 < sizeOf e) →
          panNamedExpsCost (InitECandidate.Proofs.FrontendCodecComputation.expFieldListToHOLStructural fs) = panNamedExpsCostS fs := by
        intro fs hfs
        induction fs with
        | nil => rfl
        | cons p ps ihps =>
          rcases p with ⟨fn, fv⟩
          simp only [InitECandidate.Proofs.FrontendCodecComputation.expFieldListToHOLStructural,
            InitECandidate.Proofs.FrontendCodecComputation.expFieldToHOLStructural,
            panNamedExpsCost, panNamedExpsCostS, ih fv (hfs (fn, fv) List.mem_cons_self),
            ihps (fun q hq => hfs q (List.mem_cons_of_mem _ hq))]
      cases e with
      | const _ | var _ _ | baseAddr | topAddr | bytesInWord => rfl
      | rStruct es | op _ es | panOp _ es =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, panExpCost, panExpCostS]
        exact ihm es (by intros; sizeOf_list_dec)
      | nStruct _ fs =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, panExpCost, panExpCostS]
        exact ihn fs (by intro p hp; have := List.sizeOf_lt_of_mem hp; rcases p with ⟨_, _⟩; simp only [Exp.nStruct.sizeOf_spec]; simp +arith at this ⊢; omega)
      | rField _ v | nField _ v | load _ v | load32 v | loadByte v =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, panExpCost, panExpCostS]
        exact ih v (by decreasing_trivial)
      | cmp _ a b | shift _ a b =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, panExpCost, panExpCostS]
        rw [ih a (by decreasing_trivial), ih b (by decreasing_trivial)]
  refine ⟨he, fun es => ?_⟩
  induction es with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, panExpsCost, panExpsCostS, he x, ih]

mutual
  def expFreeS {width : Nat} : (e : Exp (BitVec width)) → Bool
    | .nStruct _ _ | .nField _ _ => false
    | .rStruct fields => expsFreeS fields
    | .rField _ value => expFreeS value
    | .load shape address => shapeFreeS shape && expFreeS address
    | .loadByte address | .load32 address => expFreeS address
    | .op _ args | .panOp _ args => expsFreeS args
    | .cmp _ left right | .shift _ left right => expFreeS left && expFreeS right
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
  termination_by structural e => e

  def expsFreeS {width : Nat} : (es : List (Exp (BitVec width))) → Bool
    | [] => true
    | e :: es => expFreeS e && expsFreeS es
  termination_by structural es => es
end

theorem expFreeS_eq {width : Nat} [NeZero width] :
    (∀ e : Exp (BitVec width), expFree (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural e) = expFreeS e) ∧
    (∀ es : List (Exp (BitVec width)), expsFree (es.map InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural) = expsFreeS es) := by
  have he : ∀ e : Exp (BitVec width), expFree (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural e) = expFreeS e := by
    intro e
    induction e using (measure (sizeOf : Exp (BitVec width) → Nat)).wf.induction with
    | h e ih =>
      change ∀ c, sizeOf c < sizeOf e → expFree (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural c) = expFreeS c at ih
      have ihm : ∀ es : List (Exp (BitVec width)), (∀ x ∈ es, sizeOf x < sizeOf e) →
          expsFree (InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural es) = expsFreeS es := by
        intro es hes
        induction es with
        | nil => rfl
        | cons x xs ihxs =>
          simp only [InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
            expsFree, expsFreeS, ih x (hes x List.mem_cons_self),
            ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy))]
      cases e with
      | const _ | var _ _ | baseAddr | topAddr | bytesInWord | nStruct _ _ | nField _ _ => rfl
      | rStruct es | op _ es | panOp _ es =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, expFree, expFreeS]
        exact ihm es (by intros; sizeOf_list_dec)
      | rField _ v | load32 v | loadByte v =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, expFree, expFreeS]
        exact ih v (by decreasing_trivial)
      | load sh v =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, expFree, expFreeS,
          shapeFreeS_eq.1, ih v (by decreasing_trivial)]
      | cmp _ a b | shift _ a b =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, expFree, expFreeS,
          ih a (by decreasing_trivial), ih b (by decreasing_trivial)]
  refine ⟨he, fun es => ?_⟩
  induction es with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, expsFree, expsFreeS, he x, ih]

mutual
  def loadSafeExpS {width : Nat} : (e : Exp (BitVec width)) → Bool
    | .const _ | .var _ _ | .baseAddr | .topAddr | .bytesInWord => true
    | .rStruct es | .op _ es | .panOp _ es => loadSafeExpsS es
    | .rField _ e | .load32 e | .loadByte e | .nField _ e => loadSafeExpS e
    | .load shape e => (decide (sizeOfShapeS shape ≤ 1) || decide (panExpCostS e = 0)) && loadSafeExpS e
    | .nStruct _ fs => loadSafeNamedS fs
    | .cmp _ a b | .shift _ a b => loadSafeExpS a && loadSafeExpS b
  termination_by structural e => e

  def loadSafeExpsS {width : Nat} : (es : List (Exp (BitVec width))) → Bool
    | [] => true
    | e :: es => loadSafeExpS e && loadSafeExpsS es
  termination_by structural es => es

  def loadSafeNamedS {width : Nat} : (fs : List (String × Exp (BitVec width))) → Bool
    | [] => true
    | (_, e) :: fs => loadSafeExpS e && loadSafeNamedS fs
  termination_by structural fs => fs
end

theorem loadSafeExpS_eq {width : Nat} [NeZero width] :
    (∀ e : Exp (BitVec width), loadSafeExp (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural e) = loadSafeExpS e) ∧
    (∀ es : List (Exp (BitVec width)), loadSafeExps (es.map InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural) = loadSafeExpsS es) := by
  have he : ∀ e : Exp (BitVec width), loadSafeExp (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural e) = loadSafeExpS e := by
    intro e
    induction e using (measure (sizeOf : Exp (BitVec width) → Nat)).wf.induction with
    | h e ih =>
      change ∀ c, sizeOf c < sizeOf e → loadSafeExp (InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural c) = loadSafeExpS c at ih
      have ihm : ∀ es : List (Exp (BitVec width)), (∀ x ∈ es, sizeOf x < sizeOf e) →
          loadSafeExps (InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural es) = loadSafeExpsS es := by
        intro es hes
        induction es with
        | nil => rfl
        | cons x xs ihxs =>
          simp only [InitECandidate.Proofs.FrontendCodecComputation.expListToHOLStructural,
            loadSafeExps, loadSafeExpsS, ih x (hes x List.mem_cons_self),
            ihxs (fun y hy => hes y (List.mem_cons_of_mem _ hy))]
      have ihn : ∀ fs : List (String × Exp (BitVec width)), (∀ p ∈ fs, sizeOf p.2 < sizeOf e) →
          loadSafeNamed (InitECandidate.Proofs.FrontendCodecComputation.expFieldListToHOLStructural fs) = loadSafeNamedS fs := by
        intro fs hfs
        induction fs with
        | nil => rfl
        | cons p ps ihps =>
          rcases p with ⟨fn, fv⟩
          simp only [InitECandidate.Proofs.FrontendCodecComputation.expFieldListToHOLStructural,
            InitECandidate.Proofs.FrontendCodecComputation.expFieldToHOLStructural,
            loadSafeNamed, loadSafeNamedS, ih fv (hfs (fn, fv) List.mem_cons_self),
            ihps (fun q hq => hfs q (List.mem_cons_of_mem _ hq))]
      cases e with
      | const _ | var _ _ | baseAddr | topAddr | bytesInWord => rfl
      | rStruct es | op _ es | panOp _ es =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, loadSafeExp, loadSafeExpS]
        exact ihm es (by intros; sizeOf_list_dec)
      | nStruct _ fs =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, loadSafeExp, loadSafeExpS]
        exact ihn fs (by intro p hp; have := List.sizeOf_lt_of_mem hp; rcases p with ⟨_, _⟩; simp only [Exp.nStruct.sizeOf_spec]; simp +arith at this ⊢; omega)
      | rField _ v | nField _ v | load32 v | loadByte v =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, loadSafeExp, loadSafeExpS]
        exact ih v (by decreasing_trivial)
      | load sh v =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, loadSafeExp, loadSafeExpS,
          sizeOfShapeS_eq.1, panExpCostS_eq.1, ih v (by decreasing_trivial)]
      | cmp _ a b | shift _ a b =>
        simp only [InitECandidate.Proofs.FrontendCodecComputation.expToHOLStructural, loadSafeExp, loadSafeExpS,
          ih a (by decreasing_trivial), ih b (by decreasing_trivial)]
  refine ⟨he, fun es => ?_⟩
  induction es with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, loadSafeExps, loadSafeExpsS, he x, ih]

def panProgCostS {width : Nat} : (p : Prog (BitVec width)) → Nat
  | .skip | .break | .continue | .tick | .annot _ _ => 0
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => panExpCostS e
  | .primitive _ _ es => panExpsCostS es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => panExpCostS a + panExpCostS b
  | .dec _ _ e body => panExpCostS e + panProgCostS body
  | .decCall _ _ _ args body => panExpsCostS args + 3 + panProgCostS body
  | .seq a b => panProgCostS a + panProgCostS b
  | .ite c a b => panExpCostS c + 1 + panProgCostS a + panProgCostS b
  | .while c body => panExpCostS c + 2 + panProgCostS body
  | .extCall _ e1 e2 e3 e4 => panExpCostS e1 + panExpCostS e2 + panExpCostS e3 + panExpCostS e4
  | .call none _ args => panExpsCostS args + 3
  | .call (some (_, none)) _ args => panExpsCostS args + 3
  | .call (some (_, some (_, _, body))) _ args => panExpsCostS args + 3 + panProgCostS body
termination_by structural p => p

def progFreeS {width : Nat} : (p : Prog (BitVec width)) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => expFreeS e
  | .primitive _ _ es => expsFreeS es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => expFreeS a && expFreeS b
  | .dec _ s e body => shapeFreeS s && expFreeS e && progFreeS body
  | .decCall _ s _ args body => shapeFreeS s && expsFreeS args && progFreeS body
  | .seq a b => progFreeS a && progFreeS b
  | .ite c a b => expFreeS c && progFreeS a && progFreeS b
  | .while c body => expFreeS c && progFreeS body
  | .extCall _ e1 e2 e3 e4 => expFreeS e1 && expFreeS e2 && expFreeS e3 && expFreeS e4
  | .call none _ args => expsFreeS args
  | .call (some (_, none)) _ args => expsFreeS args
  | .call (some (_, some (_, _, body))) _ args => expsFreeS args && progFreeS body
termination_by structural p => p

def loadSafeProgS {width : Nat} : (p : Prog (BitVec width)) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ e | .return e | .raise _ e | .shMemLoad _ _ _ e => loadSafeExpS e
  | .primitive _ _ es => loadSafeExpsS es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b => loadSafeExpS a && loadSafeExpS b
  | .dec _ _ e body => loadSafeExpS e && loadSafeProgS body
  | .decCall _ _ _ args body => loadSafeExpsS args && loadSafeProgS body
  | .seq a b => loadSafeProgS a && loadSafeProgS b
  | .ite c a b => loadSafeExpS c && loadSafeProgS a && loadSafeProgS b
  | .while c body => loadSafeExpS c && loadSafeProgS body
  | .extCall _ e1 e2 e3 e4 => loadSafeExpS e1 && loadSafeExpS e2 && loadSafeExpS e3 && loadSafeExpS e4
  | .call none _ args => loadSafeExpsS args
  | .call (some (_, none)) _ args => loadSafeExpsS args
  | .call (some (_, some (_, _, body))) _ args => loadSafeExpsS args && loadSafeProgS body
termination_by structural p => p

def progNoGlobCallS {width : Nat} : (p : Prog (BitVec width)) → Bool
  | .skip | .break | .continue | .tick | .annot _ _ => true
  | .assign _ _ _ | .return _ | .raise _ _ | .primitive _ _ _ => true
  | .store _ _ | .store32 _ _ | .storeByte _ _ | .shMemStore _ _ _ | .extCall _ _ _ _ _ => true
  | .shMemLoad _ .local _ _ => true
  | .shMemLoad _ .global _ _ => false
  | .dec _ _ _ body | .decCall _ _ _ _ body | .while _ body => progNoGlobCallS body
  | .seq a b | .ite _ a b => progNoGlobCallS a && progNoGlobCallS b
  | .call none _ _ => true
  | .call (some (_, none)) _ _ => true
  | .call (some (none, some (_, _, body))) _ _ => progNoGlobCallS body
  | .call (some (some (.local, _), some (_, _, body))) _ _ => progNoGlobCallS body
  | .call (some (some (.global, _), some _)) _ _ => false
termination_by structural p => p

theorem progPredsS_eq {width : Nat} [NeZero width] :
    ∀ p : Prog (BitVec width),
      panProgCost (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural p) = panProgCostS p ∧
      progFree (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural p) = progFreeS p ∧
      loadSafeProg (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural p) = loadSafeProgS p ∧
      progNoGlobCall (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural p) = progNoGlobCallS p := by
  intro p
  induction p using (measure (sizeOf : Prog (BitVec width) → Nat)).wf.induction with
  | h p ih =>
    change ∀ q, sizeOf q < sizeOf p →
      panProgCost (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural q) = panProgCostS q ∧
      progFree (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural q) = progFreeS q ∧
      loadSafeProg (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural q) = loadSafeProgS q ∧
      progNoGlobCall (InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural q) = progNoGlobCallS q at ih
    cases p with
    | skip | «break» | «continue» | tick | annot _ _ =>
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS]
    | assign _ _ e | «return» e | raise _ e =>
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        panExpCostS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1]
    | shMemLoad _ vk _ e =>
      cases vk <;> simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        panExpCostS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1]
    | primitive _ _ es =>
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        panExpCostS_eq.2, expFreeS_eq.2, loadSafeExpS_eq.2]
    | store a b | store32 a b | storeByte a b | shMemStore _ a b =>
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        panExpCostS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1]
    | extCall _ e1 e2 e3 e4 =>
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        panExpCostS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1]
    | dec _ s e body =>
      have ihb := ih body (by decreasing_trivial)
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        shapeFreeS_eq.1, panExpCostS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1, ihb.1, ihb.2.1, ihb.2.2.1, ihb.2.2.2]
    | decCall _ s _ args body =>
      have ihb := ih body (by decreasing_trivial)
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        shapeFreeS_eq.1, panExpCostS_eq.2, expFreeS_eq.2, loadSafeExpS_eq.2, ihb.1, ihb.2.1, ihb.2.2.1, ihb.2.2.2]
    | seq a b =>
      have iha := ih a (by decreasing_trivial)
      have ihb := ih b (by decreasing_trivial)
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        iha.1, iha.2.1, iha.2.2.1, iha.2.2.2, ihb.1, ihb.2.1, ihb.2.2.1, ihb.2.2.2]
    | ite c a b =>
      have iha := ih a (by decreasing_trivial)
      have ihb := ih b (by decreasing_trivial)
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        panExpCostS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1,
        iha.1, iha.2.1, iha.2.2.1, iha.2.2.2, ihb.1, ihb.2.1, ihb.2.2.1, ihb.2.2.2]
    | «while» c body =>
      have ihb := ih body (by decreasing_trivial)
      simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
        panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
        panExpCostS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1, ihb.1, ihb.2.1, ihb.2.2.1, ihb.2.2.2]
    | call info _ args =>
      cases info with
      | none =>
        simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
          panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
          panExpCostS_eq.2, expFreeS_eq.2, loadSafeExpS_eq.2]
      | some inf =>
        rcases inf with ⟨rk, hdl⟩
        cases hdl with
        | none =>
          cases rk with
          | none =>
            simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
              panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
              panExpCostS_eq.2, expFreeS_eq.2, loadSafeExpS_eq.2]
          | some rkv =>
            rcases rkv with ⟨vk, _⟩
            cases vk <;> simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
              panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
              panExpCostS_eq.2, expFreeS_eq.2, loadSafeExpS_eq.2]
        | some hb =>
          rcases hb with ⟨eid, evar, body⟩
          have ihb := ih body (by simp_wf; omega)
          cases rk with
          | none =>
            simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
              panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
              panExpCostS_eq.2, expFreeS_eq.2, loadSafeExpS_eq.2, ihb.1, ihb.2.1, ihb.2.2.1, ihb.2.2.2]
          | some rkv =>
            rcases rkv with ⟨vk, _⟩
            cases vk <;> simp [InitECandidate.Proofs.FrontendCodecComputation.progToHOLStructural,
              panProgCost, panProgCostS, progFree, progFreeS, loadSafeProg, loadSafeProgS, progNoGlobCall, progNoGlobCallS,
              panExpCostS_eq.2, expFreeS_eq.2, loadSafeExpS_eq.2, ihb.1, ihb.2.1, ihb.2.2.1, ihb.2.2.2]

def declGoodS {width : Nat} : Decl (BitVec width) → Bool
  | .function fn =>
      !fn.inline &&
      ((fn.params.all fun p => shapeFreeS p.2) && progFreeS fn.body && shapeFreeS fn.returnShape) &&
      loadSafeProgS fn.body &&
      progNoGlobCallS fn.body &&
      decide (panProgCostS fn.body ≤ 448)
  | .decl shape _ value =>
      shapeFreeS shape && expFreeS value && loadSafeExpS value && decide (panExpCostS value = 0)
  | .exnDecl _ shape => shapeFreeS shape
  | .name _ _ => false

theorem params_shapeFree_eq :
    ∀ ps : List (String × Shape),
      ((ps.map InitECandidate.Proofs.FrontendCodecComputation.paramToHOLStructural).all fun p => shapeFree p.2) =
      (ps.all fun p => shapeFreeS p.2)
  | [] => rfl
  | p :: ps => by
    simp [InitECandidate.Proofs.FrontendCodecComputation.paramToHOLStructural,
      shapeFreeS_eq.1, params_shapeFree_eq ps]

theorem declGood_declToHOL_eq {width : Nat} [NeZero width] (d : Decl (BitVec width)) :
    declGood (declToHOL d) = declGoodS d := by
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  cases d with
  | function fn =>
    have hp := progPredsS_eq fn.body
    simp only [InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
      InitECandidate.Proofs.FrontendCodecComputation.funDeclToHOLStructural,
      declGood, declGoodS, declarationFree, params_shapeFree_eq,
      shapeFreeS_eq.1, hp.1, hp.2.1, hp.2.2.1, hp.2.2.2]
  | decl s n v =>
    simp [InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
      declGood, declGoodS, shapeFreeS_eq.1, expFreeS_eq.1, loadSafeExpS_eq.1, panExpCostS_eq.1]
  | exnDecl n s =>
    simp [InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural,
      declGood, declGoodS, shapeFreeS_eq.1]
  | name n fs => rfl

theorem all_declGood_map_declToHOL {width : Nat} [NeZero width] :
    ∀ ds : List (Decl (BitVec width)),
      (ds.map declToHOL).all declGood = ds.all declGoodS
  | [] => rfl
  | d :: ds => by simp [declGood_declToHOL_eq, all_declGood_map_declToHOL ds]

theorem guestAst_all_declGoodS : Guest.Software.guestAst.all declGoodS = true := rfl

theorem sourceDeclarations_all_declGood :
    InitE.sourceDeclarations.all declGood = true := by
  unfold InitE.sourceDeclarations
  apply mainFirstHOL_good
  rw [all_declGood_map_declToHOL]
  exact guestAst_all_declGoodS

theorem crep_listBudget_le_448 :
    listBudget ConcreteCompilerCrep.source ≤ 448 := by
  rw [← R12_Stage1To2BoundArgon.compileProgDeclsHOLW_sourceDeclarations_eq]
  have h1 := panSimpDeclsHOL_good InitE.sourceDeclarations sourceDeclarations_all_declGood
  have h2 : compileTopExact (panSimpDeclsHOL InitE.sourceDeclarations) =
      panSimpDeclsHOL InitE.sourceDeclarations :=
    compileTopExact_identity _ (all_declGood_imp_all_free _ h1)
  rw [h2]
  have h3 := compileTopExactHOL_good (panSimpDeclsHOL InitE.sourceDeclarations) (ofString "main")
    (all_declGood_imp_globalsGood _ h1)
  exact listBudget_compileProgDeclsHOLW_le_448 _ h3

theorem staticFrontBudget_sourceDeclarations_le_448 :
    staticFrontBudget InitE.sourceDeclarations (ofString "main") ≤ 448 := by
  rw [R12_Stage1To2BoundArgon.staticFrontBudget_sourceDeclarations_eq]
  exact crep_listBudget_le_448

theorem frontBudget_sourceDeclarations_le_448_proved :
    frontBudget InitE.sourceDeclarations (ofString "main") ≤ 448 :=
  R12_Stage1To2BoundArgon.frontBudget_sourceDeclarations_le_448 crep_listBudget_le_448

end InitECandidate.Solver.Wave8Stage.CrepListBudget448


