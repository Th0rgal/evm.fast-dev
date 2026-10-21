import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify367
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body383_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body383_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body383_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) body383_0 body383_1

def body383_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e") (Flapjack.Exp.const 0#64)) body383_0 body383_1

def body383_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body383_5 : Prog (BitVec 64) :=
.seq body383_3 body383_4

def body383_6 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("acct_is_empty") ([Flapjack.Exp.var Flapjack.VarKind.local "a"]) body383_5

def body383_7 : Prog (BitVec 64) :=
.seq body383_2 body383_6

def body383_8 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body383_7

def originalData383 : Decl (BitVec 64) :=
.function { name := "is_account_alive", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body383_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData383 : Decl (BitVec 64) :=
.function { name := "is_account_alive", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body383_8, returnShape := (Flapjack.Shape.one) }
def original383 := Pancake.PanLang.declToHOL originalData383
def simplified383 := Pancake.PanLang.declToHOL simplifiedData383
end InitECandidate.Proofs.FrontendStages.Declarations
