import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data372
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate356
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody372_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "acct_empty" []

def globalBody372_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody372_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) globalBody372_0 globalBody372_1

def globalBody372_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def globalBody372_4 : Prog (BitVec 64) :=
.seq globalBody372_2 globalBody372_3

def globalBody372_5 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody372_4

def globalData372 : Decl (BitVec 64) :=
.function { name := "get_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody372_5, returnShape := (Flapjack.Shape.one) }
def globalOutput372 := Pancake.PanLang.declToHOL globalData372
end InitECandidate.Proofs.FrontendStages.Declarations
