import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify236
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body252_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 0#64)

def body252_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 0#64)

def body252_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 0#64)

def body252_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "hash")

def body252_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def body252_5 : Prog (BitVec 64) :=
.seq body252_3 body252_4

def body252_6 : Prog (BitVec 64) :=
.seq body252_2 body252_5

def body252_7 : Prog (BitVec 64) :=
.seq body252_1 body252_6

def body252_8 : Prog (BitVec 64) :=
.seq body252_0 body252_7

def body252_9 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body252_8

def body252_10 : Prog (BitVec 64) :=
.seq body252_0 body252_1

def body252_11 : Prog (BitVec 64) :=
.seq body252_10 body252_2

def body252_12 : Prog (BitVec 64) :=
.seq body252_11 body252_3

def body252_13 : Prog (BitVec 64) :=
.seq body252_12 body252_4

def body252_14 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body252_13

def originalData252 : Decl (BitVec 64) :=
.function { name := "node_new_hashed", inline := false, exported := false, params := [("hash", Flapjack.Shape.one)], body := body252_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData252 : Decl (BitVec 64) :=
.function { name := "node_new_hashed", inline := false, exported := false, params := [("hash", Flapjack.Shape.one)], body := body252_14, returnShape := (Flapjack.Shape.one) }
def original252 := Pancake.PanLang.declToHOL originalData252
def simplified252 := Pancake.PanLang.declToHOL simplifiedData252
end InitECandidate.Proofs.FrontendStages.Declarations
