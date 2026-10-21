import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify258
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body274_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body274_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body274_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nc") (Flapjack.Exp.const 0#64)) body274_0 body274_1

def body274_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nc")

def body274_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "node")

def body274_5 : Prog (BitVec 64) :=
.seq body274_3 body274_4

def body274_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 3#64)) body274_5 body274_1

def body274_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def body274_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 0#64)) body274_7 body274_1

def body274_9 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat", Flapjack.Exp.var Flapjack.VarKind.local "cl",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 48#64])]

def body274_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 2#64)) body274_9 body274_1

def body274_11 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_leaf"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat", Flapjack.Exp.var Flapjack.VarKind.local "cl",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 56#64])]

def body274_12 : Prog (BitVec 64) :=
.seq body274_10 body274_11

def body274_13 : Prog (BitVec 64) :=
.dec ("cl") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "sl",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 40#64])]) body274_12

def body274_14 : Prog (BitVec 64) :=
.decCall ("cat") (Flapjack.Shape.one) ("nibbles_concat") ([Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "sl",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 40#64])]) body274_13

def body274_15 : Prog (BitVec 64) :=
.seq body274_8 body274_14

def body274_16 : Prog (BitVec 64) :=
.seq body274_6 body274_15

def body274_17 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 0#64])) body274_16

def body274_18 : Prog (BitVec 64) :=
.seq body274_2 body274_17

def body274_19 : Prog (BitVec 64) :=
.seq body274_6 body274_8

def body274_20 : Prog (BitVec 64) :=
.seq body274_19 body274_14

def body274_21 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 0#64])) body274_20

def body274_22 : Prog (BitVec 64) :=
.seq body274_2 body274_21

def originalData274 : Decl (BitVec 64) :=
.function { name := "_delete_ext_finish", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("seg", Flapjack.Shape.one), ("sl", Flapjack.Shape.one), ("nc", Flapjack.Shape.one)], body := body274_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData274 : Decl (BitVec 64) :=
.function { name := "_delete_ext_finish", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("seg", Flapjack.Shape.one), ("sl", Flapjack.Shape.one), ("nc", Flapjack.Shape.one)], body := body274_22, returnShape := (Flapjack.Shape.one) }
def original274 := Pancake.PanLang.declToHOL originalData274
def simplified274 := Pancake.PanLang.declToHOL simplifiedData274
end InitECandidate.Proofs.FrontendStages.Declarations
