import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify389
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body405_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")

def body405_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 0#64)

def body405_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")

def body405_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "l")

def body405_4 : Prog (BitVec 64) :=
.seq body405_2 body405_3

def body405_5 : Prog (BitVec 64) :=
.seq body405_1 body405_4

def body405_6 : Prog (BitVec 64) :=
.seq body405_0 body405_5

def body405_7 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "cap"]]) body405_6

def body405_8 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body405_7

def body405_9 : Prog (BitVec 64) :=
.seq body405_0 body405_1

def body405_10 : Prog (BitVec 64) :=
.seq body405_9 body405_2

def body405_11 : Prog (BitVec 64) :=
.seq body405_10 body405_3

def body405_12 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "cap"]]) body405_11

def body405_13 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 24#64]) body405_12

def originalData405 : Decl (BitVec 64) :=
.function { name := "lst_new", inline := false, exported := false, params := [("esz", Flapjack.Shape.one), ("cap", Flapjack.Shape.one)], body := body405_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData405 : Decl (BitVec 64) :=
.function { name := "lst_new", inline := false, exported := false, params := [("esz", Flapjack.Shape.one), ("cap", Flapjack.Shape.one)], body := body405_13, returnShape := (Flapjack.Shape.one) }
def original405 := Pancake.PanLang.declToHOL originalData405
def simplified405 := Pancake.PanLang.declToHOL simplifiedData405
end InitECandidate.Proofs.FrontendStages.Declarations
