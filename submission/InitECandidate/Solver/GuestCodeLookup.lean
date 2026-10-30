import InitE.SourceSemantics
import InitE.SourceNameFacts
import InitE.SourceMainFacts
import InitECandidate.Solver.CompactComputation
import InitECandidate.Solver.FrontendCodecComputation
import Flapjack.Pancake.Proofs.PanToCrep
import Flapjack.Pancake.PanToTarget.MainFirstSemantics

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace InitECandidate.Solver.GuestCodeLookup

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitE

def originalRuntimeCode : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)

theorem originalRuntimeCode_lookup_eq_reverse_lookup (f : MlS) :
    originalRuntimeCode.lookup f = List.lookup f (functionsHOL sourceDeclarations).reverse := by
  change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup f = _
  rw [HolFiniteMapExact.lookup_updateList]
  change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) f = _
  simpa only [List.reverse_reverse, FLOOKUP] using
    FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse f

private theorem lookup_of_mem_nodup {α β : Type} [BEq α] [LawfulBEq α]
    {k : α} {v : β} {l : List (α × β)}
    (hmem : (k, v) ∈ l) (hnodup : (l.map Prod.fst).Nodup) :
    List.lookup k l = some v := by
  induction l with
  | nil => cases hmem
  | cons hd tl ih =>
    obtain ⟨k', v'⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnodup
    rcases List.mem_cons.mp hmem with heq | htl
    · cases heq
      simp
    · have hne : (k == k') = false := by
        apply beq_false_of_ne
        intro h
        subst h
        exact hnodup.1 (List.mem_map.mpr ⟨(k, v), htl, rfl⟩)
      simp only [List.lookup_cons, hne]
      exact ih htl hnodup.2

theorem originalRuntimeCode_lookup_of_mem {f : MlS}
    {entry : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (hmem : (f, entry) ∈ functionsHOL sourceDeclarations) :
    originalRuntimeCode.lookup f = some entry := by
  rw [originalRuntimeCode_lookup_eq_reverse_lookup]
  apply lookup_of_mem_nodup (List.mem_reverse.mpr hmem)
  rw [List.map_reverse]
  exact List.nodup_reverse.mpr sourceDistinctFunctions

theorem mem_sourceDeclarations_of_mem {d : DeclHOL 64}
    (hmem : d ∈ Guest.Software.guestAst.map declToHOL) :
    d ∈ sourceDeclarations := by
  unfold sourceDeclarations
  obtain ⟨before, fi, rest, hsplit, _, hmoved⟩ :=
    Flapjack.Pancake.PanToTarget.mainFirstHOL_of_main
      (Guest.Software.guestAst.map declToHOL) sourceHasMain
  rw [hmoved]
  rw [hsplit] at hmem
  rcases List.mem_append.mp hmem with hb | ha
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ hb)
  · rcases List.mem_cons.mp ha with rfl | hrest
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hrest)

def sourceFunctionEntry (d : Decl (BitVec 64)) :
    MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) :=
  match InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural d with
  | .function fn => (fn.name, (fn.params, fn.body, fn.returnShape))
  | _ => (ofString "", ([], .skip, .one))

theorem mem_functionsHOL_of_mem_list (d : Decl (BitVec 64))
    (ds : List (DeclHOL 64))
    (hmem : declToHOL d ∈ ds)
    (hfn : ∃ fn, d = .function fn) :
    sourceFunctionEntry d ∈ functionsHOL ds := by
  obtain ⟨fn, rfl⟩ := hfn
  rw [InitECandidate.Solver.FrontendCodecComputation.declToHOL_eq] at hmem
  unfold sourceFunctionEntry InitECandidate.Solver.FrontendCodecComputation.declToHOLStructural at *
  induction ds with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · simp [functionsHOL]
    · cases hd <;> simp [functionsHOL, ih htl]

def extractFn (d : Decl (BitVec 64)) : FunDecl (BitVec 64) :=
  match d with
  | .function fn => fn
  | _ => { name := "", inline := false, exported := false, params := [], body := .skip, returnShape := .one }

theorem originalRuntimeCode_lookup_of_guestAst_getElem
    (i : Nat) (hi : i < Guest.Software.guestAst.length)
    (fn : FunDecl (BitVec 64))
    (hd : Guest.Software.guestAst[i] = .function fn) :
    originalRuntimeCode.lookup (ofString fn.name) =
      some (fn.params.map InitECandidate.Solver.FrontendCodecComputation.paramToHOLStructural,
        InitECandidate.Solver.FrontendCodecComputation.progToHOLStructural fn.body,
        InitECandidate.Solver.FrontendCodecComputation.shapeToHOLStructural fn.returnShape) := by
  have hmem_ast : Decl.function fn ∈ Guest.Software.guestAst := by
    rw [← hd]
    exact List.getElem_mem hi
  have hmem_map : declToHOL (Decl.function fn) ∈ Guest.Software.guestAst.map declToHOL :=
    List.mem_map_of_mem hmem_ast
  have hmem_src : declToHOL (Decl.function fn) ∈ sourceDeclarations :=
    mem_sourceDeclarations_of_mem hmem_map
  have hmem_fns := mem_functionsHOL_of_mem_list (.function fn) sourceDeclarations hmem_src ⟨fn, rfl⟩
  exact originalRuntimeCode_lookup_of_mem hmem_fns

theorem guestAst_len : Guest.Software.guestAst.length = 890 := rfl

theorem lookup_main :
    originalRuntimeCode.lookup (ofString "main") =
      some ((sourceFunctionEntry Guest.Software.guestFn_main).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 889 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_main) rfl

theorem lookup_mem_init :
    originalRuntimeCode.lookup (ofString "mem_init") =
      some ((sourceFunctionEntry Guest.Software.guestFn_mem_init).2) := by
  exact originalRuntimeCode_lookup_of_guestAst_getElem 6 (by rw [guestAst_len]; decide)
    (extractFn Guest.Software.guestFn_mem_init) rfl

end InitECandidate.Solver.GuestCodeLookup
