import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data281
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate265
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody281_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.const 0#64)

def globalBody281_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "node")

def globalBody281_2 : Prog (BitVec 64) :=
.seq globalBody281_0 globalBody281_1

def globalBody281_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 0#64)

def globalBody281_4 : Prog (BitVec 64) :=
.seq globalBody281_2 globalBody281_3

def globalBody281_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_begin"
  [Flapjack.Exp.var Flapjack.VarKind.local "fr", Flapjack.Exp.var Flapjack.VarKind.local "node"]

def globalBody281_6 : Prog (BitVec 64) :=
.seq globalBody281_4 globalBody281_5

def globalBody281_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 1#64)

def globalBody281_8 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "child"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 48#64]))

def globalBody281_9 : Prog (BitVec 64) :=
.seq globalBody281_7 globalBody281_8

def globalBody281_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "found"), none)) "_node_needs_rlp"
  [Flapjack.Exp.var Flapjack.VarKind.local "child"]

def globalBody281_11 : Prog (BitVec 64) :=
.seq globalBody281_9 globalBody281_10

def globalBody281_12 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody281_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64]))
  (Flapjack.Exp.const 0#64)) globalBody281_11 globalBody281_12

def globalBody281_14 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "child"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 32#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 8#64]]))

def globalBody281_15 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody281_16 : Prog (BitVec 64) :=
.seq globalBody281_14 globalBody281_15

def globalBody281_17 : Prog (BitVec 64) :=
.seq globalBody281_16 globalBody281_10

def globalBody281_18 : Prog (BitVec 64) :=
.while (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 16#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "found") (Flapjack.Exp.const 0#64))]) globalBody281_17

def globalBody281_19 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "i")

def globalBody281_20 : Prog (BitVec 64) :=
.seq globalBody281_18 globalBody281_19

def globalBody281_21 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 16#64])) globalBody281_20

def globalBody281_22 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 3#64)) globalBody281_21 globalBody281_12

def globalBody281_23 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "k") (Flapjack.Exp.const 2#64)) globalBody281_13 globalBody281_22

def globalBody281_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "top")

def globalBody281_25 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child")

def globalBody281_26 : Prog (BitVec 64) :=
.seq globalBody281_24 globalBody281_25

def globalBody281_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.const 0#64)

def globalBody281_28 : Prog (BitVec 64) :=
.seq globalBody281_26 globalBody281_27

def globalBody281_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_begin"
  [Flapjack.Exp.var Flapjack.VarKind.local "cf", Flapjack.Exp.var Flapjack.VarKind.local "child"]

def globalBody281_30 : Prog (BitVec 64) :=
.seq globalBody281_28 globalBody281_29

def globalBody281_31 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top" (Flapjack.Exp.var Flapjack.VarKind.local "cf")

def globalBody281_32 : Prog (BitVec 64) :=
.seq globalBody281_30 globalBody281_31

def globalBody281_33 : Prog (BitVec 64) :=
.decCall ("cf") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 48#64]) globalBody281_32

def globalBody281_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "_node_rlp_finish"
  [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.var Flapjack.VarKind.local "nd"]

def globalBody281_35 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "top"
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 0#64]))

def globalBody281_36 : Prog (BitVec 64) :=
.seq globalBody281_34 globalBody281_35

def globalBody281_37 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "found") (Flapjack.Exp.const 0#64)) globalBody281_33 globalBody281_36

def globalBody281_38 : Prog (BitVec 64) :=
.seq globalBody281_23 globalBody281_37

def globalBody281_39 : Prog (BitVec 64) :=
.dec ("found") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody281_38

def globalBody281_40 : Prog (BitVec 64) :=
.dec ("child") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody281_39

def globalBody281_41 : Prog (BitVec 64) :=
.dec ("k") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "nd", Flapjack.Exp.const 0#64])) globalBody281_40

def globalBody281_42 : Prog (BitVec 64) :=
.dec ("nd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 8#64])) globalBody281_41

def globalBody281_43 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 0#64)) globalBody281_42

def globalBody281_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "scratch_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody281_45 : Prog (BitVec 64) :=
.seq globalBody281_43 globalBody281_44

def globalBody281_46 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody281_47 : Prog (BitVec 64) :=
.seq globalBody281_45 globalBody281_46

def globalBody281_48 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "fr") globalBody281_47

def globalBody281_49 : Prog (BitVec 64) :=
.seq globalBody281_6 globalBody281_48

def globalBody281_50 : Prog (BitVec 64) :=
.decCall ("fr") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 48#64]) globalBody281_49

def globalBody281_51 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("scratch_mark") ([]) globalBody281_50

def globalData281 : Decl (BitVec 64) :=
.function { name := "_node_rlp_fill", inline := false, exported := false, params := [("node", Flapjack.Shape.one)], body := globalBody281_51, returnShape := (Flapjack.Shape.one) }
def globalOutput281 := Pancake.PanLang.declToHOL globalData281
end InitECandidate.Proofs.FrontendStages.Declarations
