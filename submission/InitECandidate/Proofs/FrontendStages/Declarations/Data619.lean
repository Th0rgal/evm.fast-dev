import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify603
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body619_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "va"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "va", Flapjack.Exp.var Flapjack.VarKind.local "vb",
      Flapjack.Exp.var Flapjack.VarKind.local "x"])

def body619_1 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "vd"
  (Flapjack.Exp.shift Flapjack.Shift.ror
    (Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.var Flapjack.VarKind.local "vd", Flapjack.Exp.var Flapjack.VarKind.local "va"])
    (Flapjack.Exp.const 32#64))

def body619_2 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "vc"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "vc", Flapjack.Exp.var Flapjack.VarKind.local "vd"])

def body619_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "vb"
  (Flapjack.Exp.shift Flapjack.Shift.ror
    (Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.var Flapjack.VarKind.local "vb", Flapjack.Exp.var Flapjack.VarKind.local "vc"])
    (Flapjack.Exp.const 24#64))

def body619_4 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "va"
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "va", Flapjack.Exp.var Flapjack.VarKind.local "vb",
      Flapjack.Exp.var Flapjack.VarKind.local "y"])

def body619_5 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "vd"
  (Flapjack.Exp.shift Flapjack.Shift.ror
    (Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.var Flapjack.VarKind.local "vd", Flapjack.Exp.var Flapjack.VarKind.local "va"])
    (Flapjack.Exp.const 16#64))

def body619_6 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "vb"
  (Flapjack.Exp.shift Flapjack.Shift.ror
    (Flapjack.Exp.op Flapjack.BinOp.xor
      [Flapjack.Exp.var Flapjack.VarKind.local "vb", Flapjack.Exp.var Flapjack.VarKind.local "vc"])
    (Flapjack.Exp.const 63#64))

def body619_7 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pa") (Flapjack.Exp.var Flapjack.VarKind.local "va")

def body619_8 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pb") (Flapjack.Exp.var Flapjack.VarKind.local "vb")

def body619_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pc") (Flapjack.Exp.var Flapjack.VarKind.local "vc")

def body619_10 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pd") (Flapjack.Exp.var Flapjack.VarKind.local "vd")

def body619_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body619_12 : Prog (BitVec 64) :=
.seq body619_10 body619_11

def body619_13 : Prog (BitVec 64) :=
.seq body619_9 body619_12

def body619_14 : Prog (BitVec 64) :=
.seq body619_8 body619_13

def body619_15 : Prog (BitVec 64) :=
.seq body619_7 body619_14

def body619_16 : Prog (BitVec 64) :=
.seq body619_6 body619_15

def body619_17 : Prog (BitVec 64) :=
.seq body619_2 body619_16

def body619_18 : Prog (BitVec 64) :=
.seq body619_5 body619_17

def body619_19 : Prog (BitVec 64) :=
.seq body619_4 body619_18

def body619_20 : Prog (BitVec 64) :=
.seq body619_3 body619_19

def body619_21 : Prog (BitVec 64) :=
.seq body619_2 body619_20

def body619_22 : Prog (BitVec 64) :=
.seq body619_1 body619_21

def body619_23 : Prog (BitVec 64) :=
.seq body619_0 body619_22

def body619_24 : Prog (BitVec 64) :=
.dec ("vd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pd")) body619_23

def body619_25 : Prog (BitVec 64) :=
.dec ("vc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pc")) body619_24

def body619_26 : Prog (BitVec 64) :=
.dec ("vb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pb")) body619_25

def body619_27 : Prog (BitVec 64) :=
.dec ("va") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pa")) body619_26

def body619_28 : Prog (BitVec 64) :=
.dec ("pd") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 8#64]]) body619_27

def body619_29 : Prog (BitVec 64) :=
.dec ("pc") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.const 8#64]]) body619_28

def body619_30 : Prog (BitVec 64) :=
.dec ("pb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 8#64]]) body619_29

def body619_31 : Prog (BitVec 64) :=
.dec ("pa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64]]) body619_30

def body619_32 : Prog (BitVec 64) :=
.seq body619_0 body619_1

def body619_33 : Prog (BitVec 64) :=
.seq body619_32 body619_2

def body619_34 : Prog (BitVec 64) :=
.seq body619_33 body619_3

def body619_35 : Prog (BitVec 64) :=
.seq body619_34 body619_4

def body619_36 : Prog (BitVec 64) :=
.seq body619_35 body619_5

def body619_37 : Prog (BitVec 64) :=
.seq body619_36 body619_2

def body619_38 : Prog (BitVec 64) :=
.seq body619_37 body619_6

def body619_39 : Prog (BitVec 64) :=
.seq body619_38 body619_7

def body619_40 : Prog (BitVec 64) :=
.seq body619_39 body619_8

def body619_41 : Prog (BitVec 64) :=
.seq body619_40 body619_9

def body619_42 : Prog (BitVec 64) :=
.seq body619_41 body619_10

def body619_43 : Prog (BitVec 64) :=
.seq body619_42 body619_11

def body619_44 : Prog (BitVec 64) :=
.dec ("vd") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pd")) body619_43

def body619_45 : Prog (BitVec 64) :=
.dec ("vc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pc")) body619_44

def body619_46 : Prog (BitVec 64) :=
.dec ("vb") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pb")) body619_45

def body619_47 : Prog (BitVec 64) :=
.dec ("va") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one (Flapjack.Exp.var Flapjack.VarKind.local "pa")) body619_46

def body619_48 : Prog (BitVec 64) :=
.dec ("pd") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 8#64]]) body619_47

def body619_49 : Prog (BitVec 64) :=
.dec ("pc") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.const 8#64]]) body619_48

def body619_50 : Prog (BitVec 64) :=
.dec ("pb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 8#64]]) body619_49

def body619_51 : Prog (BitVec 64) :=
.dec ("pa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.global "b2_v",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 8#64]]) body619_50

def originalData619 : Decl (BitVec 64) :=
.function { name := "blake2_g", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("c", Flapjack.Shape.one), ("d", Flapjack.Shape.one),
  ("x", Flapjack.Shape.one), ("y", Flapjack.Shape.one)], body := body619_31, returnShape := (Flapjack.Shape.one) }
def simplifiedData619 : Decl (BitVec 64) :=
.function { name := "blake2_g", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one), ("c", Flapjack.Shape.one), ("d", Flapjack.Shape.one),
  ("x", Flapjack.Shape.one), ("y", Flapjack.Shape.one)], body := body619_51, returnShape := (Flapjack.Shape.one) }
def original619 := Pancake.PanLang.declToHOL originalData619
def simplified619 := Pancake.PanLang.declToHOL simplifiedData619
end InitECandidate.Proofs.FrontendStages.Declarations
