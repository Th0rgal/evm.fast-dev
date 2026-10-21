import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify820
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body836_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sz" (Flapjack.Exp.const 76#64)

def body836_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body836_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 1#64)) body836_0 body836_1

def body836_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sz" (Flapjack.Exp.const 116#64)

def body836_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 2#64)) body836_3 body836_1

def body836_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sz" (Flapjack.Exp.const 184#64)

def body836_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 3#64)) body836_5 body836_1

def body836_7 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sz" (Flapjack.Exp.const 68#64)

def body836_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 4#64)) body836_7 body836_1

def body836_9 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "blob") (Flapjack.Exp.var Flapjack.VarKind.local "i")

def body836_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "blob", Flapjack.Exp.const 1#64],
    Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "cnt", Flapjack.Exp.var Flapjack.VarKind.local "sz"]]

def body836_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "arr",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 16#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "blob")

def body836_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "arr",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 16#64],
      Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "cnt", Flapjack.Exp.var Flapjack.VarKind.local "sz"],
      Flapjack.Exp.const 1#64])

def body836_13 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "n"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])

def body836_14 : Prog (BitVec 64) :=
.seq body836_12 body836_13

def body836_15 : Prog (BitVec 64) :=
.seq body836_11 body836_14

def body836_16 : Prog (BitVec 64) :=
.seq body836_10 body836_15

def body836_17 : Prog (BitVec 64) :=
.seq body836_9 body836_16

def body836_18 : Prog (BitVec 64) :=
.decCall ("blob") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "cnt", Flapjack.Exp.var Flapjack.VarKind.local "sz"],
      Flapjack.Exp.const 8#64]]) body836_17

def body836_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cnt") (Flapjack.Exp.const 0#64)) body836_18 body836_1

def body836_20 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body836_21 : Prog (BitVec 64) :=
.seq body836_19 body836_20

def body836_22 : Prog (BitVec 64) :=
.seq body836_8 body836_21

def body836_23 : Prog (BitVec 64) :=
.seq body836_6 body836_22

def body836_24 : Prog (BitVec 64) :=
.seq body836_4 body836_23

def body836_25 : Prog (BitVec 64) :=
.seq body836_2 body836_24

def body836_26 : Prog (BitVec 64) :=
.dec ("sz") (Flapjack.Shape.one) (Flapjack.Exp.const 192#64) body836_25

def body836_27 : Prog (BitVec 64) :=
.dec ("cnt") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 8#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]])) body836_26

def body836_28 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 0#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]])) body836_27

def body836_29 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 5#64)) body836_28

def body836_30 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct [Flapjack.Exp.var Flapjack.VarKind.local "arr", Flapjack.Exp.var Flapjack.VarKind.local "n"])

def body836_31 : Prog (BitVec 64) :=
.seq body836_29 body836_30

def body836_32 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body836_31

def body836_33 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body836_32

def body836_34 : Prog (BitVec 64) :=
.decCall ("arr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 16#64]]) body836_33

def body836_35 : Prog (BitVec 64) :=
.seq body836_2 body836_4

def body836_36 : Prog (BitVec 64) :=
.seq body836_35 body836_6

def body836_37 : Prog (BitVec 64) :=
.seq body836_36 body836_8

def body836_38 : Prog (BitVec 64) :=
.seq body836_9 body836_10

def body836_39 : Prog (BitVec 64) :=
.seq body836_38 body836_11

def body836_40 : Prog (BitVec 64) :=
.seq body836_39 body836_12

def body836_41 : Prog (BitVec 64) :=
.seq body836_40 body836_13

def body836_42 : Prog (BitVec 64) :=
.decCall ("blob") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "cnt", Flapjack.Exp.var Flapjack.VarKind.local "sz"],
      Flapjack.Exp.const 8#64]]) body836_41

def body836_43 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "cnt") (Flapjack.Exp.const 0#64)) body836_42 body836_1

def body836_44 : Prog (BitVec 64) :=
.seq body836_37 body836_43

def body836_45 : Prog (BitVec 64) :=
.seq body836_44 body836_20

def body836_46 : Prog (BitVec 64) :=
.dec ("sz") (Flapjack.Shape.one) (Flapjack.Exp.const 192#64) body836_45

def body836_47 : Prog (BitVec 64) :=
.dec ("cnt") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 8#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]])) body836_46

def body836_48 : Prog (BitVec 64) :=
.dec ("p") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 0#64,
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 16#64]])) body836_47

def body836_49 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 5#64)) body836_48

def body836_50 : Prog (BitVec 64) :=
.seq body836_49 body836_30

def body836_51 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body836_50

def body836_52 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body836_51

def body836_53 : Prog (BitVec 64) :=
.decCall ("arr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 16#64]]) body836_52

def originalData836 : Decl (BitVec 64) :=
.function { name := "encode_execution_requests", inline := false, exported := false, params := [("rq", Flapjack.Shape.one)], body := body836_34, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData836 : Decl (BitVec 64) :=
.function { name := "encode_execution_requests", inline := false, exported := false, params := [("rq", Flapjack.Shape.one)], body := body836_53, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original836 := Pancake.PanLang.declToHOL originalData836
def simplified836 := Pancake.PanLang.declToHOL simplifiedData836
end InitECandidate.Proofs.FrontendStages.Declarations
