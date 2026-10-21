import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify651
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body667_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]]

def body667_1 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "d")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def body667_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body667_3 : Prog (BitVec 64) :=
.seq body667_1 body667_2

def body667_4 : Prog (BitVec 64) :=
.seq body667_0 body667_3

def body667_5 : Prog (BitVec 64) :=
.seq body667_0 body667_1

def body667_6 : Prog (BitVec 64) :=
.seq body667_5 body667_2

def originalData667 : Decl (BitVec 64) :=
.function { name := "fe_set_one", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("d", Flapjack.Shape.one)], body := body667_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData667 : Decl (BitVec 64) :=
.function { name := "fe_set_one", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("d", Flapjack.Shape.one)], body := body667_6, returnShape := (Flapjack.Shape.one) }
def original667 := Pancake.PanLang.declToHOL originalData667
def simplified667 := Pancake.PanLang.declToHOL simplifiedData667
end InitECandidate.Proofs.FrontendStages.Declarations
