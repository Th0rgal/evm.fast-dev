import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data383
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate367
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody383_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody383_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody383_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "a") (Flapjack.Exp.const 1#64)) globalBody383_0 globalBody383_1

def globalBody383_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e") (Flapjack.Exp.const 0#64)) globalBody383_0 globalBody383_1

def globalBody383_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody383_5 : Prog (BitVec 64) :=
.seq globalBody383_3 globalBody383_4

def globalBody383_6 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("acct_is_empty") ([Flapjack.Exp.var Flapjack.VarKind.local "a"]) globalBody383_5

def globalBody383_7 : Prog (BitVec 64) :=
.seq globalBody383_2 globalBody383_6

def globalBody383_8 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody383_7

def globalData383 : Decl (BitVec 64) :=
.function { name := "is_account_alive", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody383_8, returnShape := (Flapjack.Shape.one) }
def globalOutput383 := Pancake.PanLang.declToHOL globalData383
end InitECandidate.Proofs.FrontendStages.Declarations
