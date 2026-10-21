import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify729
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body745_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body745_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64]]

def body745_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body745_3 : Prog (BitVec 64) :=
.seq body745_1 body745_2

def body745_4 : Prog (BitVec 64) :=
.seq body745_0 body745_3

def body745_5 : Prog (BitVec 64) :=
.seq body745_0 body745_1

def body745_6 : Prog (BitVec 64) :=
.seq body745_5 body745_2

def originalData745 : Decl (BitVec 64) :=
.function { name := "fp12_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body745_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData745 : Decl (BitVec 64) :=
.function { name := "fp12_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body745_6, returnShape := (Flapjack.Shape.one) }
def original745 := Pancake.PanLang.declToHOL originalData745
def simplified745 := Pancake.PanLang.declToHOL simplifiedData745
end InitECandidate.Proofs.FrontendStages.Declarations
