import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify738
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body754_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "f"]

def body754_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.local "f"]

def body754_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body754_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m"]

def body754_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body754_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "m"]

def body754_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m"]

def body754_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body754_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body754_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body754_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body754_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body754_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "b",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body754_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body754_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "c"]

def body754_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body754_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body754_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body754_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.var Flapjack.VarKind.local "m"]

def body754_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "m"]

def body754_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body754_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body754_22 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body754_23 : Prog (BitVec 64) :=
.seq body754_21 body754_22

def body754_24 : Prog (BitVec 64) :=
.seq body754_20 body754_23

def body754_25 : Prog (BitVec 64) :=
.seq body754_19 body754_24

def body754_26 : Prog (BitVec 64) :=
.seq body754_18 body754_25

def body754_27 : Prog (BitVec 64) :=
.seq body754_16 body754_26

def body754_28 : Prog (BitVec 64) :=
.seq body754_17 body754_27

def body754_29 : Prog (BitVec 64) :=
.seq body754_16 body754_28

def body754_30 : Prog (BitVec 64) :=
.seq body754_4 body754_29

def body754_31 : Prog (BitVec 64) :=
.seq body754_15 body754_30

def body754_32 : Prog (BitVec 64) :=
.seq body754_14 body754_31

def body754_33 : Prog (BitVec 64) :=
.seq body754_13 body754_32

def body754_34 : Prog (BitVec 64) :=
.seq body754_12 body754_33

def body754_35 : Prog (BitVec 64) :=
.seq body754_11 body754_34

def body754_36 : Prog (BitVec 64) :=
.seq body754_10 body754_35

def body754_37 : Prog (BitVec 64) :=
.seq body754_7 body754_36

def body754_38 : Prog (BitVec 64) :=
.seq body754_9 body754_37

def body754_39 : Prog (BitVec 64) :=
.seq body754_8 body754_38

def body754_40 : Prog (BitVec 64) :=
.seq body754_7 body754_39

def body754_41 : Prog (BitVec 64) :=
.seq body754_6 body754_40

def body754_42 : Prog (BitVec 64) :=
.seq body754_5 body754_41

def body754_43 : Prog (BitVec 64) :=
.seq body754_2 body754_42

def body754_44 : Prog (BitVec 64) :=
.seq body754_4 body754_43

def body754_45 : Prog (BitVec 64) :=
.seq body754_3 body754_44

def body754_46 : Prog (BitVec 64) :=
.seq body754_2 body754_45

def body754_47 : Prog (BitVec 64) :=
.seq body754_1 body754_46

def body754_48 : Prog (BitVec 64) :=
.seq body754_0 body754_47

def body754_49 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 2304#64]) body754_48

def body754_50 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1728#64]) body754_49

def body754_51 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1152#64]) body754_50

def body754_52 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body754_51

def body754_53 : Prog (BitVec 64) :=
.dec ("m") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body754_52

def body754_54 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 576#64, Flapjack.Exp.const 5#64]]) body754_53

def body754_55 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body754_54

def body754_56 : Prog (BitVec 64) :=
.seq body754_0 body754_1

def body754_57 : Prog (BitVec 64) :=
.seq body754_56 body754_2

def body754_58 : Prog (BitVec 64) :=
.seq body754_57 body754_3

def body754_59 : Prog (BitVec 64) :=
.seq body754_58 body754_4

def body754_60 : Prog (BitVec 64) :=
.seq body754_59 body754_2

def body754_61 : Prog (BitVec 64) :=
.seq body754_60 body754_5

def body754_62 : Prog (BitVec 64) :=
.seq body754_61 body754_6

def body754_63 : Prog (BitVec 64) :=
.seq body754_62 body754_7

def body754_64 : Prog (BitVec 64) :=
.seq body754_63 body754_8

def body754_65 : Prog (BitVec 64) :=
.seq body754_64 body754_9

def body754_66 : Prog (BitVec 64) :=
.seq body754_65 body754_7

def body754_67 : Prog (BitVec 64) :=
.seq body754_66 body754_10

def body754_68 : Prog (BitVec 64) :=
.seq body754_67 body754_11

def body754_69 : Prog (BitVec 64) :=
.seq body754_68 body754_12

def body754_70 : Prog (BitVec 64) :=
.seq body754_69 body754_13

def body754_71 : Prog (BitVec 64) :=
.seq body754_70 body754_14

def body754_72 : Prog (BitVec 64) :=
.seq body754_71 body754_15

def body754_73 : Prog (BitVec 64) :=
.seq body754_72 body754_4

def body754_74 : Prog (BitVec 64) :=
.seq body754_73 body754_16

def body754_75 : Prog (BitVec 64) :=
.seq body754_74 body754_17

def body754_76 : Prog (BitVec 64) :=
.seq body754_75 body754_16

def body754_77 : Prog (BitVec 64) :=
.seq body754_76 body754_18

def body754_78 : Prog (BitVec 64) :=
.seq body754_77 body754_19

def body754_79 : Prog (BitVec 64) :=
.seq body754_78 body754_20

def body754_80 : Prog (BitVec 64) :=
.seq body754_79 body754_21

def body754_81 : Prog (BitVec 64) :=
.seq body754_80 body754_22

def body754_82 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 2304#64]) body754_81

def body754_83 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1728#64]) body754_82

def body754_84 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1152#64]) body754_83

def body754_85 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body754_84

def body754_86 : Prog (BitVec 64) :=
.dec ("m") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body754_85

def body754_87 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 576#64, Flapjack.Exp.const 5#64]]) body754_86

def body754_88 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body754_87

def originalData754 : Decl (BitVec 64) :=
.function { name := "fp12_final_exp", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("f", Flapjack.Shape.one)], body := body754_55, returnShape := (Flapjack.Shape.one) }
def simplifiedData754 : Decl (BitVec 64) :=
.function { name := "fp12_final_exp", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("f", Flapjack.Shape.one)], body := body754_88, returnShape := (Flapjack.Shape.one) }
def original754 := Pancake.PanLang.declToHOL originalData754
def simplified754 := Pancake.PanLang.declToHOL simplifiedData754
end InitECandidate.Proofs.FrontendStages.Declarations
