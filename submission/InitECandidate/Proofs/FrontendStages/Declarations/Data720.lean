import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify704
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body720_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
      Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
      Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64])

def body720_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body720_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body720_3 : Prog (BitVec 64) :=
.seq body720_1 body720_2

def body720_4 : Prog (BitVec 64) :=
.seq body720_0 body720_3

def body720_5 : Prog (BitVec 64) :=
.seq body720_0 body720_1

def body720_6 : Prog (BitVec 64) :=
.seq body720_5 body720_2

def originalData720 : Decl (BitVec 64) :=
.function { name := "fp2_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body720_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData720 : Decl (BitVec 64) :=
.function { name := "fp2_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body720_6, returnShape := (Flapjack.Shape.one) }
def original720 := Pancake.PanLang.declToHOL originalData720
def simplified720 := Pancake.PanLang.declToHOL simplifiedData720
end InitECandidate.Proofs.FrontendStages.Declarations
