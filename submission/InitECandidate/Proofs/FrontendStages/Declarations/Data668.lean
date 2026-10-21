import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify652
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body668_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "pt"]

def body668_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_one"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def body668_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "pt",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]

def body668_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body668_4 : Prog (BitVec 64) :=
.seq body668_2 body668_3

def body668_5 : Prog (BitVec 64) :=
.seq body668_1 body668_4

def body668_6 : Prog (BitVec 64) :=
.seq body668_0 body668_5

def body668_7 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) body668_6

def body668_8 : Prog (BitVec 64) :=
.seq body668_0 body668_1

def body668_9 : Prog (BitVec 64) :=
.seq body668_8 body668_2

def body668_10 : Prog (BitVec 64) :=
.seq body668_9 body668_3

def body668_11 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) body668_10

def originalData668 : Decl (BitVec 64) :=
.function { name := "ecp_set_inf", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("pt", Flapjack.Shape.one)], body := body668_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData668 : Decl (BitVec 64) :=
.function { name := "ecp_set_inf", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("pt", Flapjack.Shape.one)], body := body668_11, returnShape := (Flapjack.Shape.one) }
def original668 := Pancake.PanLang.declToHOL originalData668
def simplified668 := Pancake.PanLang.declToHOL simplifiedData668
end InitECandidate.Proofs.FrontendStages.Declarations
