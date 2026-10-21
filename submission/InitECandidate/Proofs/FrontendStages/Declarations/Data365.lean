import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify349
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body365_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "m"), Flapjack.Exp.const 1#64])

def body365_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body365_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "m"))
  (Flapjack.Exp.const 0#64)) body365_0 body365_1

def body365_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "root",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 1#64]]

def body365_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "node")

def body365_5 : Prog (BitVec 64) :=
.seq body365_3 body365_4

def body365_6 : Prog (BitVec 64) :=
.decCall ("node") (Flapjack.Shape.one) ("decode_witness_to_mpt") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 0#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "root"]) body365_5

def body365_7 : Prog (BitVec 64) :=
.seq body365_2 body365_6

def body365_8 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_get") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "root"]) body365_7

def body365_9 : Prog (BitVec 64) :=
.dec ("t") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 32#64])) body365_8

def originalData365 : Decl (BitVec 64) :=
.function { name := "ws_storage_trie", inline := false, exported := false, params := [("root", Flapjack.Shape.one)], body := body365_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData365 : Decl (BitVec 64) :=
.function { name := "ws_storage_trie", inline := false, exported := false, params := [("root", Flapjack.Shape.one)], body := body365_9, returnShape := (Flapjack.Shape.one) }
def original365 := Pancake.PanLang.declToHOL originalData365
def simplified365 := Pancake.PanLang.declToHOL simplifiedData365
end InitECandidate.Proofs.FrontendStages.Declarations
