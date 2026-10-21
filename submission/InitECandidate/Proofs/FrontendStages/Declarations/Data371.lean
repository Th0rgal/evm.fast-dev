import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify355
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body371_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 1#64]

def body371_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w"))

def body371_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body371_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "w"))
  (Flapjack.Exp.const 0#64)) body371_1 body371_2

def body371_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body371_5 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_pre_state_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body371_4

def body371_6 : Prog (BitVec 64) :=
.seq body371_3 body371_5

def body371_7 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body371_6

def body371_8 : Prog (BitVec 64) :=
.seq body371_0 body371_7

def originalData371 : Decl (BitVec 64) :=
.function { name := "get_account_optional", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body371_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData371 : Decl (BitVec 64) :=
.function { name := "get_account_optional", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body371_8, returnShape := (Flapjack.Shape.one) }
def original371 := Pancake.PanLang.declToHOL originalData371
def simplified371 := Pancake.PanLang.declToHOL simplifiedData371
end InitECandidate.Proofs.FrontendStages.Declarations
