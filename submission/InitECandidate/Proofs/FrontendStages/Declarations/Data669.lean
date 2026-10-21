import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify653
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body669_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "fe_is_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "pt",
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.const 2#64,
            Flapjack.Exp.panOp Flapjack.PanOp.mul
              [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]]]]

def originalData669 : Decl (BitVec 64) :=
.function { name := "ecp_is_inf", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("pt", Flapjack.Shape.one)], body := body669_0, returnShape := (Flapjack.Shape.one) }
def simplifiedData669 : Decl (BitVec 64) :=
.function { name := "ecp_is_inf", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("pt", Flapjack.Shape.one)], body := body669_0, returnShape := (Flapjack.Shape.one) }
def original669 := Pancake.PanLang.declToHOL originalData669
def simplified669 := Pancake.PanLang.declToHOL simplifiedData669
end InitECandidate.Proofs.FrontendStages.Declarations
