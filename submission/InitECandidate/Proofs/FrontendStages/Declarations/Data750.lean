import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify734
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body750_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body750_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64]]

def body750_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul_v"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body750_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body750_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "d"]

def body750_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "d"]

def body750_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64],
    Flapjack.Exp.var Flapjack.VarKind.local "d"]

def body750_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_neg"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64]]

def body750_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body750_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body750_10 : Prog (BitVec 64) :=
.seq body750_8 body750_9

def body750_11 : Prog (BitVec 64) :=
.seq body750_7 body750_10

def body750_12 : Prog (BitVec 64) :=
.seq body750_6 body750_11

def body750_13 : Prog (BitVec 64) :=
.seq body750_5 body750_12

def body750_14 : Prog (BitVec 64) :=
.seq body750_4 body750_13

def body750_15 : Prog (BitVec 64) :=
.seq body750_3 body750_14

def body750_16 : Prog (BitVec 64) :=
.seq body750_2 body750_15

def body750_17 : Prog (BitVec 64) :=
.seq body750_1 body750_16

def body750_18 : Prog (BitVec 64) :=
.seq body750_0 body750_17

def body750_19 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body750_18

def body750_20 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body750_19

def body750_21 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body750_20

def body750_22 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 288#64, Flapjack.Exp.const 3#64]]) body750_21

def body750_23 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body750_22

def body750_24 : Prog (BitVec 64) :=
.seq body750_0 body750_1

def body750_25 : Prog (BitVec 64) :=
.seq body750_24 body750_2

def body750_26 : Prog (BitVec 64) :=
.seq body750_25 body750_3

def body750_27 : Prog (BitVec 64) :=
.seq body750_26 body750_4

def body750_28 : Prog (BitVec 64) :=
.seq body750_27 body750_5

def body750_29 : Prog (BitVec 64) :=
.seq body750_28 body750_6

def body750_30 : Prog (BitVec 64) :=
.seq body750_29 body750_7

def body750_31 : Prog (BitVec 64) :=
.seq body750_30 body750_8

def body750_32 : Prog (BitVec 64) :=
.seq body750_31 body750_9

def body750_33 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body750_32

def body750_34 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body750_33

def body750_35 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body750_34

def body750_36 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 288#64, Flapjack.Exp.const 3#64]]) body750_35

def body750_37 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body750_36

def originalData750 : Decl (BitVec 64) :=
.function { name := "fp12_inv", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body750_23, returnShape := (Flapjack.Shape.one) }
def simplifiedData750 : Decl (BitVec 64) :=
.function { name := "fp12_inv", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body750_37, returnShape := (Flapjack.Shape.one) }
def original750 := Pancake.PanLang.declToHOL originalData750
def simplified750 := Pancake.PanLang.declToHOL simplifiedData750
end InitECandidate.Proofs.FrontendStages.Declarations
