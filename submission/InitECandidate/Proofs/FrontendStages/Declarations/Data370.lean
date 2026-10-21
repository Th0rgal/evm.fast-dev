import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify354
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body370_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "acct_empty" []

def body370_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body370_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) body370_0 body370_1

def body370_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body370_4 : Prog (BitVec 64) :=
.seq body370_2 body370_3

def body370_5 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_pre_state_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body370_4

def originalData370 : Decl (BitVec 64) :=
.function { name := "get_pre_state_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body370_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData370 : Decl (BitVec 64) :=
.function { name := "get_pre_state_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body370_5, returnShape := (Flapjack.Shape.one) }
def original370 := Pancake.PanLang.declToHOL originalData370
def simplified370 := Pancake.PanLang.declToHOL simplifiedData370
end InitECandidate.Proofs.FrontendStages.Declarations
