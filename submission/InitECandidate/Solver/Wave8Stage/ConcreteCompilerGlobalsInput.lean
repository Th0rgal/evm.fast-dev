import InitECandidate.Solver.Wave8Stage.ConcreteCompilerStruct
import InitECandidate.Solver.Wave8Stage.CertifiedApplication

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200000
set_option maxHeartbeats 4000000
set_option cbv.maxSteps 10000000

namespace InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsInput
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

noncomputable def head : FunDeclHOL 64 :=
  match ConcreteCompilerStruct.source with
  | .function function :: _ => function
  | _ => {
      name := ofString ""
      inline := false
      exported := false
      params := []
      body := .skip
      returnShape := .one }

noncomputable def tail := ConcreteCompilerStruct.source.tail

theorem codeShape : ConcreteCompilerStruct.source = .function head :: tail := by rfl
theorem headName : head.name = ofString "main" := by rfl
theorem headParams : head.params = [] := by rfl
wave8_expose shape := head.returnShape until Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact

theorem headShape : head.returnShape = .one := by
  apply shape_eq.trans
  have one : shape.last = .one := by
    change shapeToHOL Flapjack.Shape.one = .one
    exact shapeToHOL.eq_1
  change Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact shape.arg1 shape.last = .one
  rw [one]
  exact Flapjack.Pancake.PanStructs.CompileShapeExact.compileShapeExact.eq_1 _

#print axioms codeShape
#print axioms headName
#print axioms headParams
#print axioms headShape
end InitECandidate.Solver.Wave8Stage.ConcreteCompilerGlobalsInput
