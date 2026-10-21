import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify731
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body747_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body747_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 288#64]]

def body747_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "sa", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64]]

def body747_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "sb", Flapjack.Exp.var Flapjack.VarKind.local "b",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 288#64]]

def body747_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "sa",
    Flapjack.Exp.var Flapjack.VarKind.local "sb"]

def body747_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "t0"]

def body747_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_sub"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body747_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul_v"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body747_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body747_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body747_10 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body747_11 : Prog (BitVec 64) :=
.seq body747_9 body747_10

def body747_12 : Prog (BitVec 64) :=
.seq body747_8 body747_11

def body747_13 : Prog (BitVec 64) :=
.seq body747_7 body747_12

def body747_14 : Prog (BitVec 64) :=
.seq body747_6 body747_13

def body747_15 : Prog (BitVec 64) :=
.seq body747_5 body747_14

def body747_16 : Prog (BitVec 64) :=
.seq body747_4 body747_15

def body747_17 : Prog (BitVec 64) :=
.seq body747_3 body747_16

def body747_18 : Prog (BitVec 64) :=
.seq body747_2 body747_17

def body747_19 : Prog (BitVec 64) :=
.seq body747_1 body747_18

def body747_20 : Prog (BitVec 64) :=
.seq body747_0 body747_19

def body747_21 : Prog (BitVec 64) :=
.dec ("sb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1152#64]) body747_20

def body747_22 : Prog (BitVec 64) :=
.dec ("sa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 864#64]) body747_21

def body747_23 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body747_22

def body747_24 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body747_23

def body747_25 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body747_24

def body747_26 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 288#64, Flapjack.Exp.const 5#64]]) body747_25

def body747_27 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body747_26

def body747_28 : Prog (BitVec 64) :=
.seq body747_0 body747_1

def body747_29 : Prog (BitVec 64) :=
.seq body747_28 body747_2

def body747_30 : Prog (BitVec 64) :=
.seq body747_29 body747_3

def body747_31 : Prog (BitVec 64) :=
.seq body747_30 body747_4

def body747_32 : Prog (BitVec 64) :=
.seq body747_31 body747_5

def body747_33 : Prog (BitVec 64) :=
.seq body747_32 body747_6

def body747_34 : Prog (BitVec 64) :=
.seq body747_33 body747_7

def body747_35 : Prog (BitVec 64) :=
.seq body747_34 body747_8

def body747_36 : Prog (BitVec 64) :=
.seq body747_35 body747_9

def body747_37 : Prog (BitVec 64) :=
.seq body747_36 body747_10

def body747_38 : Prog (BitVec 64) :=
.dec ("sb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1152#64]) body747_37

def body747_39 : Prog (BitVec 64) :=
.dec ("sa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 864#64]) body747_38

def body747_40 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body747_39

def body747_41 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body747_40

def body747_42 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body747_41

def body747_43 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 288#64, Flapjack.Exp.const 5#64]]) body747_42

def body747_44 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body747_43

def originalData747 : Decl (BitVec 64) :=
.function { name := "fp12_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body747_27, returnShape := (Flapjack.Shape.one) }
def simplifiedData747 : Decl (BitVec 64) :=
.function { name := "fp12_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body747_44, returnShape := (Flapjack.Shape.one) }
def original747 := Pancake.PanLang.declToHOL originalData747
def simplified747 := Pancake.PanLang.declToHOL simplifiedData747
end InitECandidate.Proofs.FrontendStages.Declarations
