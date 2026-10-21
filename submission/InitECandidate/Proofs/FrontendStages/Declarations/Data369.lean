import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify353
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body369_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 1#64]

def body369_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "w"))

def body369_2 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body369_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "w"))
  (Flapjack.Exp.const 0#64)) body369_1 body369_2

def body369_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "record_pre_state_read" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def body369_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body369_6 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("ws_get_account_optional") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body369_5

def body369_7 : Prog (BitVec 64) :=
.seq body369_4 body369_6

def body369_8 : Prog (BitVec 64) :=
.seq body369_3 body369_7

def body369_9 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body369_8

def body369_10 : Prog (BitVec 64) :=
.seq body369_0 body369_9

def body369_11 : Prog (BitVec 64) :=
.seq body369_3 body369_4

def body369_12 : Prog (BitVec 64) :=
.seq body369_11 body369_6

def body369_13 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 16#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body369_12

def body369_14 : Prog (BitVec 64) :=
.seq body369_0 body369_13

def originalData369 : Decl (BitVec 64) :=
.function { name := "get_pre_state_account_optional", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body369_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData369 : Decl (BitVec 64) :=
.function { name := "get_pre_state_account_optional", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body369_14, returnShape := (Flapjack.Shape.one) }
def original369 := Pancake.PanLang.declToHOL originalData369
def simplified369 := Pancake.PanLang.declToHOL simplifiedData369
end InitECandidate.Proofs.FrontendStages.Declarations
