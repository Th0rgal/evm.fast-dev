import InitECandidate.Solver.Wave8Stage.GlobalDeclarationComposition

set_option autoImplicit false

namespace InitECandidate.Solver.Wave8Stage.GlobalTopComposition
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

def build {width : Nat} [NeZero width] (fresh : MlS)
    (result : List (ProgHOL width) × List (DeclHOL width) × List (DeclHOL width) × PanGlobalsContextExact width) :
    List (DeclHOL width) :=
  result.snd.snd.fst ++ DeclHOL.function {
    name := ofString "main"
    inline := false
    exported := false
    params := []
    body := .seq (nestedSeqHOL result.fst) (.call none fresh [])
    returnShape := .one } :: result.snd.fst

theorem assemble {width : Nat} [NeZero width]
    (code : List (DeclHOL width)) (head : FunDeclHOL width) (tail : List (DeclHOL width))
    (resorted renamed : List (DeclHOL width)) (fresh : MlS) (initial : PanGlobalsContextExact width)
    (compiled : List (ProgHOL width) × List (DeclHOL width) × List (DeclHOL width) × PanGlobalsContextExact width)
    (codeShape : code = .function head :: tail)
    (headName : head.name = ofString "main") (headParams : head.params = [])
    (headShape : head.returnShape = .one)
    (sortRun : resortDeclsHOL code = resorted) (freshRun : newMainNameHOL code = fresh)
    (renameRun : fpermDecsHOL (ofString "main") fresh resorted = renamed)
    (initRun : ({
      globals := HolFiniteMapExact.empty
      globalsSize := 0
      maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum
      } : PanGlobalsContextExact width) = initial)
    (compiledRun : compileDecsExactHOL initial renamed = compiled) :
    compileTopExactHOL code (ofString "main") = build fresh compiled := by
  rcases head with ⟨name,inl,exported,parameters,body,shape⟩
  dsimp only at headName headParams headShape
  subst name
  subst parameters
  subst shape
  subst code
  let original : List (DeclHOL width) := .function {
    name := ofString "main"
    inline := inl
    exported := exported
    params := []
    body := body
    returnShape := .one } :: tail
  change (let renamed := fpermDecsHOL (ofString "main") (newMainNameHOL original) (resortDeclsHOL original);
    let initial : PanGlobalsContextExact width := {
      globals := HolFiniteMapExact.empty
      globalsSize := 0
      maxGlobalsSize := cakeBytesInWord width * BitVec.ofNat width ((decShapesHOL renamed).map sizeOfShapeHOL).sum };
    build (newMainNameHOL original) (compileDecsExactHOL initial renamed)) = build fresh compiled
  dsimp only
  rw [freshRun,sortRun,renameRun,initRun,compiledRun]

#print axioms assemble
end InitECandidate.Solver.Wave8Stage.GlobalTopComposition
