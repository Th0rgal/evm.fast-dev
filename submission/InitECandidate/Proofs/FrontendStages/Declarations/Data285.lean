import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify269
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body285_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "cached")

def body285_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body285_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cached") (Flapjack.Exp.const 0#64)) body285_0 body285_1

def body285_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 13#64]

def body285_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) body285_3 body285_1

def body285_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body285_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "h")

def body285_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "h")

def body285_8 : Prog (BitVec 64) :=
.seq body285_6 body285_7

def body285_9 : Prog (BitVec 64) :=
.seq body285_5 body285_8

def body285_10 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body285_9

def body285_11 : Prog (BitVec 64) :=
.seq body285_4 body285_10

def body285_12 : Prog (BitVec 64) :=
.seq body285_2 body285_11

def body285_13 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])) body285_12

def body285_14 : Prog (BitVec 64) :=
.seq body285_2 body285_4

def body285_15 : Prog (BitVec 64) :=
.seq body285_5 body285_6

def body285_16 : Prog (BitVec 64) :=
.seq body285_15 body285_7

def body285_17 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body285_16

def body285_18 : Prog (BitVec 64) :=
.seq body285_14 body285_17

def body285_19 : Prog (BitVec 64) :=
.dec ("cached") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 24#64])) body285_18

def originalData285 : Decl (BitVec 64) :=
.function { name := "node_hash_cached", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body285_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData285 : Decl (BitVec 64) :=
.function { name := "node_hash_cached", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body285_19, returnShape := (Flapjack.Shape.one) }
def original285 := Pancake.PanLang.declToHOL originalData285
def simplified285 := Pancake.PanLang.declToHOL simplifiedData285
end InitECandidate.Proofs.FrontendStages.Declarations
