import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify739
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body755_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
      Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
      Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64])

def body755_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
      Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
      Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64])

def body755_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body755_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body755_4 : Prog (BitVec 64) :=
.seq body755_2 body755_3

def body755_5 : Prog (BitVec 64) :=
.seq body755_1 body755_4

def body755_6 : Prog (BitVec 64) :=
.seq body755_0 body755_5

def body755_7 : Prog (BitVec 64) :=
.seq body755_0 body755_1

def body755_8 : Prog (BitVec 64) :=
.seq body755_7 body755_2

def body755_9 : Prog (BitVec 64) :=
.seq body755_8 body755_3

def originalData755 : Decl (BitVec 64) :=
.function { name := "g1_set_inf", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body755_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData755 : Decl (BitVec 64) :=
.function { name := "g1_set_inf", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body755_9, returnShape := (Flapjack.Shape.one) }
def original755 := Pancake.PanLang.declToHOL originalData755
def simplified755 := Pancake.PanLang.declToHOL simplifiedData755
end InitECandidate.Proofs.FrontendStages.Declarations
