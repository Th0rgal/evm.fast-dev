import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify363
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body379_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body379_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body379_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"), Flapjack.Exp.const 24#64]))) body379_0 body379_1

def body379_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) body379_2 body379_1

def body379_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "m"), none)) "htab_get"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bs", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def body379_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "record_pre_state_read" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def body379_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body379_7 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.one) ("ws_account_has_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body379_6

def body379_8 : Prog (BitVec 64) :=
.seq body379_5 body379_7

def body379_9 : Prog (BitVec 64) :=
.seq body379_3 body379_8

def body379_10 : Prog (BitVec 64) :=
.seq body379_4 body379_9

def body379_11 : Prog (BitVec 64) :=
.seq body379_3 body379_10

def body379_12 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body379_11

def body379_13 : Prog (BitVec 64) :=
.seq body379_3 body379_4

def body379_14 : Prog (BitVec 64) :=
.seq body379_13 body379_3

def body379_15 : Prog (BitVec 64) :=
.seq body379_14 body379_5

def body379_16 : Prog (BitVec 64) :=
.seq body379_15 body379_7

def body379_17 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "addr"]) body379_16

def originalData379 : Decl (BitVec 64) :=
.function { name := "account_has_storage", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body379_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData379 : Decl (BitVec 64) :=
.function { name := "account_has_storage", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body379_17, returnShape := (Flapjack.Shape.one) }
def original379 := Pancake.PanLang.declToHOL originalData379
def simplified379 := Pancake.PanLang.declToHOL simplifiedData379
end InitECandidate.Proofs.FrontendStages.Declarations
