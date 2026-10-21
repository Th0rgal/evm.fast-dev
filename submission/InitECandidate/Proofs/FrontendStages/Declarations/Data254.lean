import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify238
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body254_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 2#64)

def body254_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.const 0#64)

def body254_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 0#64)

def body254_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 24#64])
  (Flapjack.Exp.const 0#64)

def body254_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nib")

def body254_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nlen")

def body254_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child")

def body254_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "nd")

def body254_8 : Prog (BitVec 64) :=
.seq body254_6 body254_7

def body254_9 : Prog (BitVec 64) :=
.seq body254_5 body254_8

def body254_10 : Prog (BitVec 64) :=
.seq body254_4 body254_9

def body254_11 : Prog (BitVec 64) :=
.seq body254_3 body254_10

def body254_12 : Prog (BitVec 64) :=
.seq body254_2 body254_11

def body254_13 : Prog (BitVec 64) :=
.seq body254_1 body254_12

def body254_14 : Prog (BitVec 64) :=
.seq body254_0 body254_13

def body254_15 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 56#64]) body254_14

def body254_16 : Prog (BitVec 64) :=
.seq body254_0 body254_1

def body254_17 : Prog (BitVec 64) :=
.seq body254_16 body254_2

def body254_18 : Prog (BitVec 64) :=
.seq body254_17 body254_3

def body254_19 : Prog (BitVec 64) :=
.seq body254_18 body254_4

def body254_20 : Prog (BitVec 64) :=
.seq body254_19 body254_5

def body254_21 : Prog (BitVec 64) :=
.seq body254_20 body254_6

def body254_22 : Prog (BitVec 64) :=
.seq body254_21 body254_7

def body254_23 : Prog (BitVec 64) :=
.decCall ("nd") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 56#64]) body254_22

def originalData254 : Decl (BitVec 64) :=
.function { name := "node_new_ext", inline := false, exported := false, params := [("nib", Flapjack.Shape.one), ("nlen", Flapjack.Shape.one), ("child", Flapjack.Shape.one)], body := body254_15, returnShape := (Flapjack.Shape.one) }
def simplifiedData254 : Decl (BitVec 64) :=
.function { name := "node_new_ext", inline := false, exported := false, params := [("nib", Flapjack.Shape.one), ("nlen", Flapjack.Shape.one), ("child", Flapjack.Shape.one)], body := body254_23, returnShape := (Flapjack.Shape.one) }
def original254 := Pancake.PanLang.declToHOL originalData254
def simplified254 := Pancake.PanLang.declToHOL simplifiedData254
end InitECandidate.Proofs.FrontendStages.Declarations
