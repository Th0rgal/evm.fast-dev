import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify373
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body389_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "destroy_storage" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def body389_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "acct_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body389_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 0#64)

def body389_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash")

def body389_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "modify_state_commit"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body389_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body389_6 : Prog (BitVec 64) :=
.seq body389_4 body389_5

def body389_7 : Prog (BitVec 64) :=
.seq body389_3 body389_6

def body389_8 : Prog (BitVec 64) :=
.seq body389_2 body389_7

def body389_9 : Prog (BitVec 64) :=
.seq body389_1 body389_8

def body389_10 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body389_9

def body389_11 : Prog (BitVec 64) :=
.seq body389_0 body389_10

def body389_12 : Prog (BitVec 64) :=
.seq body389_1 body389_2

def body389_13 : Prog (BitVec 64) :=
.seq body389_12 body389_3

def body389_14 : Prog (BitVec 64) :=
.seq body389_13 body389_4

def body389_15 : Prog (BitVec 64) :=
.seq body389_14 body389_5

def body389_16 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body389_15

def body389_17 : Prog (BitVec 64) :=
.seq body389_0 body389_16

def originalData389 : Decl (BitVec 64) :=
.function { name := "clear_account_preserving_balance", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body389_11, returnShape := (Flapjack.Shape.one) }
def simplifiedData389 : Decl (BitVec 64) :=
.function { name := "clear_account_preserving_balance", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body389_17, returnShape := (Flapjack.Shape.one) }
def original389 := Pancake.PanLang.declToHOL originalData389
def simplified389 := Pancake.PanLang.declToHOL simplifiedData389
end InitECandidate.Proofs.FrontendStages.Declarations
