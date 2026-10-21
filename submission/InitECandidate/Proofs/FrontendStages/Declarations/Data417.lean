import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify401
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body417_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w"))

def body417_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body417_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "w"))
  (Flapjack.Exp.const 0#64)) body417_0 body417_1

def body417_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "record_pre_state_read" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def body417_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body417_5 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("ws_get_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body417_4

def body417_6 : Prog (BitVec 64) :=
.seq body417_3 body417_5

def body417_7 : Prog (BitVec 64) :=
.seq body417_2 body417_6

def body417_8 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body417_7

def body417_9 : Prog (BitVec 64) :=
.seq body417_2 body417_3

def body417_10 : Prog (BitVec 64) :=
.seq body417_9 body417_5

def body417_11 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body417_10

def originalData417 : Decl (BitVec 64) :=
.function { name := "get_pre_tx_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body417_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData417 : Decl (BitVec 64) :=
.function { name := "get_pre_tx_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body417_11, returnShape := (Flapjack.Shape.one) }
def original417 := Pancake.PanLang.declToHOL originalData417
def simplified417 := Pancake.PanLang.declToHOL simplifiedData417
end InitECandidate.Proofs.FrontendStages.Declarations
