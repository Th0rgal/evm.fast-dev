import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify356
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body372_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "acct_empty" []

def body372_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body372_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) body372_0 body372_1

def body372_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body372_4 : Prog (BitVec 64) :=
.seq body372_2 body372_3

def body372_5 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body372_4

def originalData372 : Decl (BitVec 64) :=
.function { name := "get_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body372_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData372 : Decl (BitVec 64) :=
.function { name := "get_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body372_5, returnShape := (Flapjack.Shape.one) }
def original372 := Pancake.PanLang.declToHOL originalData372
def simplified372 := Pancake.PanLang.declToHOL simplifiedData372
end InitECandidate.Proofs.FrontendStages.Declarations
