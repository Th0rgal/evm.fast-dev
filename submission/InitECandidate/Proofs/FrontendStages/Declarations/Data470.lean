import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify454
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body470_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 100#64)

def body470_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body470_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "w") (Flapjack.Exp.const 0#64)) body470_0 body470_1

def body470_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 3000#64)

def body470_4 : Prog (BitVec 64) :=
.seq body470_2 body470_3

def body470_5 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.one) ("is_warm_address") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body470_4

def originalData470 : Decl (BitVec 64) :=
.function { name := "access_gas_cost", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body470_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData470 : Decl (BitVec 64) :=
.function { name := "access_gas_cost", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body470_5, returnShape := (Flapjack.Shape.one) }
def original470 := Pancake.PanLang.declToHOL originalData470
def simplified470 := Pancake.PanLang.declToHOL simplifiedData470
end InitECandidate.Proofs.FrontendStages.Declarations
