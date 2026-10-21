import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify237
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body253_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 1#64)

def body253_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 0#64)

def body253_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 0#64)

def body253_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 0#64)

def body253_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nib")

def body253_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nlen")

def body253_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vptr")

def body253_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 56#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "vlen")

def body253_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def body253_9 : Prog (BitVec 64) :=
.seq body253_7 body253_8

def body253_10 : Prog (BitVec 64) :=
.seq body253_6 body253_9

def body253_11 : Prog (BitVec 64) :=
.seq body253_5 body253_10

def body253_12 : Prog (BitVec 64) :=
.seq body253_4 body253_11

def body253_13 : Prog (BitVec 64) :=
.seq body253_3 body253_12

def body253_14 : Prog (BitVec 64) :=
.seq body253_2 body253_13

def body253_15 : Prog (BitVec 64) :=
.seq body253_1 body253_14

def body253_16 : Prog (BitVec 64) :=
.seq body253_0 body253_15

def body253_17 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body253_16

def body253_18 : Prog (BitVec 64) :=
.seq body253_0 body253_1

def body253_19 : Prog (BitVec 64) :=
.seq body253_18 body253_2

def body253_20 : Prog (BitVec 64) :=
.seq body253_19 body253_3

def body253_21 : Prog (BitVec 64) :=
.seq body253_20 body253_4

def body253_22 : Prog (BitVec 64) :=
.seq body253_21 body253_5

def body253_23 : Prog (BitVec 64) :=
.seq body253_22 body253_6

def body253_24 : Prog (BitVec 64) :=
.seq body253_23 body253_7

def body253_25 : Prog (BitVec 64) :=
.seq body253_24 body253_8

def body253_26 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body253_25

def originalData253 : Decl (BitVec 64) :=
.function { name := "node_new_leaf", inline := false, exported := false, params := [("nib", Flapjack.Shape.one), ("nlen", Flapjack.Shape.one), ("vptr", Flapjack.Shape.one), ("vlen", Flapjack.Shape.one)], body := body253_17, returnShape := (Flapjack.Shape.one) }
def simplifiedData253 : Decl (BitVec 64) :=
.function { name := "node_new_leaf", inline := false, exported := false, params := [("nib", Flapjack.Shape.one), ("nlen", Flapjack.Shape.one), ("vptr", Flapjack.Shape.one), ("vlen", Flapjack.Shape.one)], body := body253_26, returnShape := (Flapjack.Shape.one) }
def original253 := Pancake.PanLang.declToHOL originalData253
def simplified253 := Pancake.PanLang.declToHOL simplifiedData253
end InitECandidate.Proofs.FrontendStages.Declarations
