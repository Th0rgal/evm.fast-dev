import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify847
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body863_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body863_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body863_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 4#64)) body863_0 body863_1

def body863_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body863_4 : Prog (BitVec 64) :=
.seq body863_2 body863_3

def originalData863 : Decl (BitVec 64) :=
.function { name := "tx_is_setcode", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body863_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData863 : Decl (BitVec 64) :=
.function { name := "tx_is_setcode", inline := false, exported := false, params := [("tx", Flapjack.Shape.one)], body := body863_4, returnShape := (Flapjack.Shape.one) }
def original863 := Pancake.PanLang.declToHOL originalData863
def simplified863 := Pancake.PanLang.declToHOL simplifiedData863
end InitECandidate.Proofs.FrontendStages.Declarations
