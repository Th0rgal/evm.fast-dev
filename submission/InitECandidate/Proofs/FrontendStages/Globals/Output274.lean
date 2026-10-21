import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data274
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate258
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody274_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody274_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody274_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "nc") (Flapjack.Exp.const 0#64)) globalBody274_0 globalBody274_1

def globalBody274_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nc")

def globalBody274_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody274_5 : Prog (BitVec 64) :=
.seq globalBody274_3 globalBody274_4

def globalBody274_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 3#64)) globalBody274_5 globalBody274_1

def globalBody274_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def globalBody274_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 0#64)) globalBody274_7 globalBody274_1

def globalBody274_9 : Prog (BitVec 64) :=
.seq globalBody274_6 globalBody274_8

def globalBody274_10 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat", Flapjack.Exp.var Flapjack.VarKind.local "cl",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 48#64])]

def globalBody274_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 2#64)) globalBody274_10 globalBody274_1

def globalBody274_12 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_leaf"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat", Flapjack.Exp.var Flapjack.VarKind.local "cl",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 56#64])]

def globalBody274_13 : Prog (BitVec 64) :=
.seq globalBody274_11 globalBody274_12

def globalBody274_14 : Prog (BitVec 64) :=
.dec ("cl") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "sl",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 40#64])]) globalBody274_13

def globalBody274_15 : Prog (BitVec 64) :=
.decCall ("cat") (Flapjack.Shape.one) ("nibbles_concat") ([Flapjack.Exp.var Flapjack.VarKind.local "seg", Flapjack.Exp.var Flapjack.VarKind.local "sl",
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 40#64])]) globalBody274_14

def globalBody274_16 : Prog (BitVec 64) :=
.seq globalBody274_9 globalBody274_15

def globalBody274_17 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nc", Flapjack.Exp.const 0#64])) globalBody274_16

def globalBody274_18 : Prog (BitVec 64) :=
.seq globalBody274_2 globalBody274_17

def globalData274 : Decl (BitVec 64) :=
.function { name := "_delete_ext_finish", inline := false, exported := false, params := [("node", Flapjack.Shape.one), ("seg", Flapjack.Shape.one), ("sl", Flapjack.Shape.one), ("nc", Flapjack.Shape.one)], body := globalBody274_18, returnShape := (Flapjack.Shape.one) }
def globalOutput274 := Pancake.PanLang.declToHOL globalData274
end InitECandidate.Proofs.FrontendStages.Declarations
