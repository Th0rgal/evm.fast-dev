import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify390
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body406_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")

def body406_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 0#64)

def body406_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")

def body406_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "l")

def body406_4 : Prog (BitVec 64) :=
.seq body406_2 body406_3

def body406_5 : Prog (BitVec 64) :=
.seq body406_1 body406_4

def body406_6 : Prog (BitVec 64) :=
.seq body406_0 body406_5

def body406_7 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "cap"]]) body406_6

def body406_8 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 24#64]) body406_7

def body406_9 : Prog (BitVec 64) :=
.seq body406_0 body406_1

def body406_10 : Prog (BitVec 64) :=
.seq body406_9 body406_2

def body406_11 : Prog (BitVec 64) :=
.seq body406_10 body406_3

def body406_12 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "cap"]]) body406_11

def body406_13 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 24#64]) body406_12

def originalData406 : Decl (BitVec 64) :=
.function { name := "lst_new_scratch", inline := false, exported := false, params := [("esz", Flapjack.Shape.one), ("cap", Flapjack.Shape.one)], body := body406_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData406 : Decl (BitVec 64) :=
.function { name := "lst_new_scratch", inline := false, exported := false, params := [("esz", Flapjack.Shape.one), ("cap", Flapjack.Shape.one)], body := body406_13, returnShape := (Flapjack.Shape.one) }
def original406 := Pancake.PanLang.declToHOL originalData406
def simplified406 := Pancake.PanLang.declToHOL simplifiedData406
end InitECandidate.Proofs.FrontendStages.Declarations
