import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify271
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body287_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "cached")

def body287_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body287_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cached") (Flapjack.Exp.const 0#64)) body287_0 body287_1

def body287_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "r"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "r"), Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body287_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "h")

def body287_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "h")

def body287_6 : Prog (BitVec 64) :=
.seq body287_4 body287_5

def body287_7 : Prog (BitVec 64) :=
.seq body287_3 body287_6

def body287_8 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body287_7

def body287_9 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("node_rlp") ([Flapjack.Exp.var Flapjack.VarKind.local "node"]) body287_8

def body287_10 : Prog (BitVec 64) :=
.seq body287_2 body287_9

def body287_11 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])) body287_10

def body287_12 : Prog (BitVec 64) :=
.seq body287_3 body287_4

def body287_13 : Prog (BitVec 64) :=
.seq body287_12 body287_5

def body287_14 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body287_13

def body287_15 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("node_rlp") ([Flapjack.Exp.var Flapjack.VarKind.local "node"]) body287_14

def body287_16 : Prog (BitVec 64) :=
.seq body287_2 body287_15

def body287_17 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])) body287_16

def originalData287 : Decl (BitVec 64) :=
.function { name := "node_hash", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body287_11, returnShape := (Flapjack.Shape.one) }
def simplifiedData287 : Decl (BitVec 64) :=
.function { name := "node_hash", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body287_17, returnShape := (Flapjack.Shape.one) }
def original287 := Pancake.PanLang.declToHOL originalData287
def simplified287 := Pancake.PanLang.declToHOL simplifiedData287
end InitECandidate.Proofs.FrontendStages.Declarations
