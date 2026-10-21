import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify724
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body740_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body740_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 96#64]]

def body740_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 192#64]]

def body740_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body740_4 : Prog (BitVec 64) :=
.seq body740_2 body740_3

def body740_5 : Prog (BitVec 64) :=
.seq body740_1 body740_4

def body740_6 : Prog (BitVec 64) :=
.seq body740_0 body740_5

def body740_7 : Prog (BitVec 64) :=
.seq body740_0 body740_1

def body740_8 : Prog (BitVec 64) :=
.seq body740_7 body740_2

def body740_9 : Prog (BitVec 64) :=
.seq body740_8 body740_3

def originalData740 : Decl (BitVec 64) :=
.function { name := "fp6_neg", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body740_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData740 : Decl (BitVec 64) :=
.function { name := "fp6_neg", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body740_9, returnShape := (Flapjack.Shape.one) }
def original740 := Pancake.PanLang.declToHOL originalData740
def simplified740 := Pancake.PanLang.declToHOL simplifiedData740
end InitECandidate.Proofs.FrontendStages.Declarations
