import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify378
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body394_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "acct_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body394_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")

def body394_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modify_state_commit"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body394_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body394_4 : Prog (BitVec 64) :=
.seq body394_2 body394_3

def body394_5 : Prog (BitVec 64) :=
.seq body394_1 body394_4

def body394_6 : Prog (BitVec 64) :=
.seq body394_0 body394_5

def body394_7 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body394_6

def body394_8 : Prog (BitVec 64) :=
.seq body394_0 body394_1

def body394_9 : Prog (BitVec 64) :=
.seq body394_8 body394_2

def body394_10 : Prog (BitVec 64) :=
.seq body394_9 body394_3

def body394_11 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body394_10

def originalData394 : Decl (BitVec 64) :=
.function { name := "set_account_balance", inline := false, exported := false, params := [("addr", Flapjack.Shape.one),
  ("amount", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body394_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData394 : Decl (BitVec 64) :=
.function { name := "set_account_balance", inline := false, exported := false, params := [("addr", Flapjack.Shape.one),
  ("amount", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body394_11, returnShape := (Flapjack.Shape.one) }
def original394 := Pancake.PanLang.declToHOL originalData394
def simplified394 := Pancake.PanLang.declToHOL simplifiedData394
end InitECandidate.Proofs.FrontendStages.Declarations
