import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify346
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body362_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 20#64,
    Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body362_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body362_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def body362_3 : Prog (BitVec 64) :=
.seq body362_1 body362_2

def body362_4 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("trie_lookup") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ws", Flapjack.Exp.const 24#64]),
  Flapjack.Exp.var Flapjack.VarKind.local "h"]) body362_3

def body362_5 : Prog (BitVec 64) :=
.seq body362_0 body362_4

def body362_6 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body362_5

def body362_7 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body362_6

def originalData362 : Decl (BitVec 64) :=
.function { name := "ws_account_leaf", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body362_7, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData362 : Decl (BitVec 64) :=
.function { name := "ws_account_leaf", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body362_7, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original362 := Pancake.PanLang.declToHOL originalData362
def simplified362 := Pancake.PanLang.declToHOL simplifiedData362
end InitECandidate.Proofs.FrontendStages.Declarations
