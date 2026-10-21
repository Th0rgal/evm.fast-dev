import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data273
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate257
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody273_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "count", Flapjack.Exp.const 1#64])

def globalBody273_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "idx" (Flapjack.Exp.var Flapjack.VarKind.local "i")

def globalBody273_2 : Prog (BitVec 64) :=
.seq globalBody273_0 globalBody273_1

def globalBody273_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody273_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]))
  (Flapjack.Exp.const 0#64)) globalBody273_2 globalBody273_3

def globalBody273_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody273_6 : Prog (BitVec 64) :=
.seq globalBody273_4 globalBody273_5

def globalBody273_7 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)) globalBody273_6

def globalBody273_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 12#64]

def globalBody273_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vl") (Flapjack.Exp.const 0#64)) globalBody273_8 globalBody273_3

def globalBody273_10 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_leaf"
  [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 160#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "vl"]

def globalBody273_11 : Prog (BitVec 64) :=
.seq globalBody273_9 globalBody273_10

def globalBody273_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "count") (Flapjack.Exp.const 0#64)) globalBody273_11 globalBody273_3

def globalBody273_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def globalBody273_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 0#64)) globalBody273_13 globalBody273_3

def globalBody273_15 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "nib") (Flapjack.Exp.var Flapjack.VarKind.local "idx")

def globalBody273_16 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "nib", Flapjack.Exp.const 1#64,
    Flapjack.Exp.var Flapjack.VarKind.local "child"]

def globalBody273_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 3#64)) globalBody273_16 globalBody273_3

def globalBody273_18 : Prog (BitVec 64) :=
.seq globalBody273_15 globalBody273_17

def globalBody273_19 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_leaf"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.const 1#64,
        Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 40#64])],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 56#64])]

def globalBody273_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 1#64)) globalBody273_19 globalBody273_3

def globalBody273_21 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.const 1#64,
        Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 40#64])],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 48#64])]

def globalBody273_22 : Prog (BitVec 64) :=
.seq globalBody273_20 globalBody273_21

def globalBody273_23 : Prog (BitVec 64) :=
.decCall ("cat") (Flapjack.Shape.one) ("nibbles_concat") ([Flapjack.Exp.var Flapjack.VarKind.local "nib", Flapjack.Exp.const 1#64,
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 40#64])]) globalBody273_22

def globalBody273_24 : Prog (BitVec 64) :=
.seq globalBody273_18 globalBody273_23

def globalBody273_25 : Prog (BitVec 64) :=
.decCall ("nib") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) globalBody273_24

def globalBody273_26 : Prog (BitVec 64) :=
.seq globalBody273_14 globalBody273_25

def globalBody273_27 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64])) globalBody273_26

def globalBody273_28 : Prog (BitVec 64) :=
.dec ("child") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]])) globalBody273_27

def globalBody273_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "count") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vl") (Flapjack.Exp.const 0#64))]) globalBody273_28 globalBody273_3

def globalBody273_30 : Prog (BitVec 64) :=
.seq globalBody273_12 globalBody273_29

def globalBody273_31 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody273_32 : Prog (BitVec 64) :=
.seq globalBody273_30 globalBody273_31

def globalBody273_33 : Prog (BitVec 64) :=
.dec ("vl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64])) globalBody273_32

def globalBody273_34 : Prog (BitVec 64) :=
.seq globalBody273_7 globalBody273_33

def globalBody273_35 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody273_34

def globalBody273_36 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody273_35

def globalBody273_37 : Prog (BitVec 64) :=
.dec ("count") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody273_36

def globalData273 : Decl (BitVec 64) :=
.function { name := "_collapse_branch", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := globalBody273_37, returnShape := (Flapjack.Shape.one) }
def globalOutput273 := Pancake.PanLang.declToHOL globalData273
end InitECandidate.Proofs.FrontendStages.Declarations
