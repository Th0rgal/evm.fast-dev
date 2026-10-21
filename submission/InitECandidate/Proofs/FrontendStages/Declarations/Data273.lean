import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify257
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body273_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "count"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "count", Flapjack.Exp.const 1#64])

def body273_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "idx" (Flapjack.Exp.var Flapjack.VarKind.local "i")

def body273_2 : Prog (BitVec 64) :=
.seq body273_0 body273_1

def body273_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body273_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]))
  (Flapjack.Exp.const 0#64)) body273_2 body273_3

def body273_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body273_6 : Prog (BitVec 64) :=
.seq body273_4 body273_5

def body273_7 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)) body273_6

def body273_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 12#64]

def body273_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vl") (Flapjack.Exp.const 0#64)) body273_8 body273_3

def body273_10 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_leaf"
  [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 0#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 160#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "vl"]

def body273_11 : Prog (BitVec 64) :=
.seq body273_9 body273_10

def body273_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "count") (Flapjack.Exp.const 0#64)) body273_11 body273_3

def body273_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 2#64]

def body273_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 0#64)) body273_13 body273_3

def body273_15 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "nib") (Flapjack.Exp.var Flapjack.VarKind.local "idx")

def body273_16 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "nib", Flapjack.Exp.const 1#64,
    Flapjack.Exp.var Flapjack.VarKind.local "child"]

def body273_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 3#64)) body273_16 body273_3

def body273_18 : Prog (BitVec 64) :=
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

def body273_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ck") (Flapjack.Exp.const 1#64)) body273_18 body273_3

def body273_20 : Prog (BitVec 64) :=
Flapjack.Prog.call none "node_new_ext"
  [Flapjack.Exp.var Flapjack.VarKind.local "cat",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.const 1#64,
        Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 40#64])],
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 48#64])]

def body273_21 : Prog (BitVec 64) :=
.seq body273_19 body273_20

def body273_22 : Prog (BitVec 64) :=
.decCall ("cat") (Flapjack.Shape.one) ("nibbles_concat") ([Flapjack.Exp.var Flapjack.VarKind.local "nib", Flapjack.Exp.const 1#64,
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 32#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 40#64])]) body273_21

def body273_23 : Prog (BitVec 64) :=
.seq body273_17 body273_22

def body273_24 : Prog (BitVec 64) :=
.seq body273_15 body273_23

def body273_25 : Prog (BitVec 64) :=
.decCall ("nib") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body273_24

def body273_26 : Prog (BitVec 64) :=
.seq body273_14 body273_25

def body273_27 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64])) body273_26

def body273_28 : Prog (BitVec 64) :=
.dec ("child") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]])) body273_27

def body273_29 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "count") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vl") (Flapjack.Exp.const 0#64))]) body273_28 body273_3

def body273_30 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "node")

def body273_31 : Prog (BitVec 64) :=
.seq body273_29 body273_30

def body273_32 : Prog (BitVec 64) :=
.seq body273_12 body273_31

def body273_33 : Prog (BitVec 64) :=
.dec ("vl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64])) body273_32

def body273_34 : Prog (BitVec 64) :=
.seq body273_7 body273_33

def body273_35 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body273_34

def body273_36 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body273_35

def body273_37 : Prog (BitVec 64) :=
.dec ("count") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body273_36

def body273_38 : Prog (BitVec 64) :=
.seq body273_15 body273_17

def body273_39 : Prog (BitVec 64) :=
.seq body273_38 body273_22

def body273_40 : Prog (BitVec 64) :=
.decCall ("nib") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 8#64]) body273_39

def body273_41 : Prog (BitVec 64) :=
.seq body273_14 body273_40

def body273_42 : Prog (BitVec 64) :=
.dec ("ck") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64])) body273_41

def body273_43 : Prog (BitVec 64) :=
.dec ("child") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 32#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "idx", Flapjack.Exp.const 8#64]])) body273_42

def body273_44 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "count") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "vl") (Flapjack.Exp.const 0#64))]) body273_43 body273_3

def body273_45 : Prog (BitVec 64) :=
.seq body273_12 body273_44

def body273_46 : Prog (BitVec 64) :=
.seq body273_45 body273_30

def body273_47 : Prog (BitVec 64) :=
.dec ("vl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "node", Flapjack.Exp.const 168#64])) body273_46

def body273_48 : Prog (BitVec 64) :=
.seq body273_7 body273_47

def body273_49 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body273_48

def body273_50 : Prog (BitVec 64) :=
.dec ("idx") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body273_49

def body273_51 : Prog (BitVec 64) :=
.dec ("count") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body273_50

def originalData273 : Decl (BitVec 64) :=
.function { name := "_collapse_branch", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body273_37, returnShape := (Flapjack.Shape.one) }
def simplifiedData273 : Decl (BitVec 64) :=
.function { name := "_collapse_branch", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := body273_51, returnShape := (Flapjack.Shape.one) }
def original273 := Pancake.PanLang.declToHOL originalData273
def simplified273 := Pancake.PanLang.declToHOL simplifiedData273
end InitECandidate.Proofs.FrontendStages.Declarations
