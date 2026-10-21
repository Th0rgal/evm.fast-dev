import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify727
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body743_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body743_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 192#64]]

def body743_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul_xi"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body743_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body743_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 192#64]]

def body743_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul_xi"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body743_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 96#64]]

def body743_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body743_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 96#64]]

def body743_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 192#64]]

def body743_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body743_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body743_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body743_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body743_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul_xi"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "d"]

def body743_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "t0"]

def body743_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "di", Flapjack.Exp.var Flapjack.VarKind.local "d"]

def body743_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "di"]

def body743_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "di"]

def body743_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "di"]

def body743_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body743_21 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body743_22 : Prog (BitVec 64) :=
.seq body743_20 body743_21

def body743_23 : Prog (BitVec 64) :=
.seq body743_19 body743_22

def body743_24 : Prog (BitVec 64) :=
.seq body743_18 body743_23

def body743_25 : Prog (BitVec 64) :=
.seq body743_17 body743_24

def body743_26 : Prog (BitVec 64) :=
.seq body743_16 body743_25

def body743_27 : Prog (BitVec 64) :=
.seq body743_13 body743_26

def body743_28 : Prog (BitVec 64) :=
.seq body743_15 body743_27

def body743_29 : Prog (BitVec 64) :=
.seq body743_14 body743_28

def body743_30 : Prog (BitVec 64) :=
.seq body743_13 body743_29

def body743_31 : Prog (BitVec 64) :=
.seq body743_12 body743_30

def body743_32 : Prog (BitVec 64) :=
.seq body743_11 body743_31

def body743_33 : Prog (BitVec 64) :=
.seq body743_10 body743_32

def body743_34 : Prog (BitVec 64) :=
.seq body743_9 body743_33

def body743_35 : Prog (BitVec 64) :=
.seq body743_8 body743_34

def body743_36 : Prog (BitVec 64) :=
.seq body743_7 body743_35

def body743_37 : Prog (BitVec 64) :=
.seq body743_6 body743_36

def body743_38 : Prog (BitVec 64) :=
.seq body743_5 body743_37

def body743_39 : Prog (BitVec 64) :=
.seq body743_4 body743_38

def body743_40 : Prog (BitVec 64) :=
.seq body743_3 body743_39

def body743_41 : Prog (BitVec 64) :=
.seq body743_2 body743_40

def body743_42 : Prog (BitVec 64) :=
.seq body743_1 body743_41

def body743_43 : Prog (BitVec 64) :=
.seq body743_0 body743_42

def body743_44 : Prog (BitVec 64) :=
.dec ("di") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body743_43

def body743_45 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body743_44

def body743_46 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body743_45

def body743_47 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body743_46

def body743_48 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body743_47

def body743_49 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body743_48

def body743_50 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 6#64]]) body743_49

def body743_51 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body743_50

def body743_52 : Prog (BitVec 64) :=
.seq body743_0 body743_1

def body743_53 : Prog (BitVec 64) :=
.seq body743_52 body743_2

def body743_54 : Prog (BitVec 64) :=
.seq body743_53 body743_3

def body743_55 : Prog (BitVec 64) :=
.seq body743_54 body743_4

def body743_56 : Prog (BitVec 64) :=
.seq body743_55 body743_5

def body743_57 : Prog (BitVec 64) :=
.seq body743_56 body743_6

def body743_58 : Prog (BitVec 64) :=
.seq body743_57 body743_7

def body743_59 : Prog (BitVec 64) :=
.seq body743_58 body743_8

def body743_60 : Prog (BitVec 64) :=
.seq body743_59 body743_9

def body743_61 : Prog (BitVec 64) :=
.seq body743_60 body743_10

def body743_62 : Prog (BitVec 64) :=
.seq body743_61 body743_11

def body743_63 : Prog (BitVec 64) :=
.seq body743_62 body743_12

def body743_64 : Prog (BitVec 64) :=
.seq body743_63 body743_13

def body743_65 : Prog (BitVec 64) :=
.seq body743_64 body743_14

def body743_66 : Prog (BitVec 64) :=
.seq body743_65 body743_15

def body743_67 : Prog (BitVec 64) :=
.seq body743_66 body743_13

def body743_68 : Prog (BitVec 64) :=
.seq body743_67 body743_16

def body743_69 : Prog (BitVec 64) :=
.seq body743_68 body743_17

def body743_70 : Prog (BitVec 64) :=
.seq body743_69 body743_18

def body743_71 : Prog (BitVec 64) :=
.seq body743_70 body743_19

def body743_72 : Prog (BitVec 64) :=
.seq body743_71 body743_20

def body743_73 : Prog (BitVec 64) :=
.seq body743_72 body743_21

def body743_74 : Prog (BitVec 64) :=
.dec ("di") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body743_73

def body743_75 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body743_74

def body743_76 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body743_75

def body743_77 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body743_76

def body743_78 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body743_77

def body743_79 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body743_78

def body743_80 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 6#64]]) body743_79

def body743_81 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body743_80

def originalData743 : Decl (BitVec 64) :=
.function { name := "fp6_inv", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body743_51, returnShape := (Flapjack.Shape.one) }
def simplifiedData743 : Decl (BitVec 64) :=
.function { name := "fp6_inv", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body743_81, returnShape := (Flapjack.Shape.one) }
def original743 := Pancake.PanLang.declToHOL originalData743
def simplified743 := Pancake.PanLang.declToHOL simplifiedData743
end InitECandidate.Proofs.FrontendStages.Declarations
