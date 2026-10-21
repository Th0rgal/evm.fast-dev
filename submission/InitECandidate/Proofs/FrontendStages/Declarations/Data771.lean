import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify755
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body771_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body771_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body771_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body771_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.var Flapjack.VarKind.local "y",
    Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body771_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "x",
    Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body771_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "b",
    Flapjack.Exp.var Flapjack.VarKind.local "s"]

def body771_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "b",
    Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body771_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body771_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body771_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "nx", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body771_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "nx",
    Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body771_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "s2", Flapjack.Exp.var Flapjack.VarKind.local "s"]

def body771_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "nx", Flapjack.Exp.var Flapjack.VarKind.local "h",
    Flapjack.Exp.var Flapjack.VarKind.local "s"]

def body771_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "nx", Flapjack.Exp.var Flapjack.VarKind.local "nx",
    Flapjack.Exp.var Flapjack.VarKind.local "nx"]

def body771_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "h"]

def body771_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "ny", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body771_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body771_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "s2"]

def body771_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ny", Flapjack.Exp.var Flapjack.VarKind.local "ny",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body771_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "s",
    Flapjack.Exp.var Flapjack.VarKind.local "s2"]

def body771_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "nx"]

def body771_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "ny"]

def body771_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body771_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body771_24 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body771_25 : Prog (BitVec 64) :=
.seq body771_23 body771_24

def body771_26 : Prog (BitVec 64) :=
.seq body771_22 body771_25

def body771_27 : Prog (BitVec 64) :=
.seq body771_21 body771_26

def body771_28 : Prog (BitVec 64) :=
.seq body771_20 body771_27

def body771_29 : Prog (BitVec 64) :=
.seq body771_7 body771_28

def body771_30 : Prog (BitVec 64) :=
.seq body771_7 body771_29

def body771_31 : Prog (BitVec 64) :=
.seq body771_7 body771_30

def body771_32 : Prog (BitVec 64) :=
.seq body771_19 body771_31

def body771_33 : Prog (BitVec 64) :=
.seq body771_18 body771_32

def body771_34 : Prog (BitVec 64) :=
.seq body771_7 body771_33

def body771_35 : Prog (BitVec 64) :=
.seq body771_7 body771_34

def body771_36 : Prog (BitVec 64) :=
.seq body771_7 body771_35

def body771_37 : Prog (BitVec 64) :=
.seq body771_17 body771_36

def body771_38 : Prog (BitVec 64) :=
.seq body771_16 body771_37

def body771_39 : Prog (BitVec 64) :=
.seq body771_15 body771_38

def body771_40 : Prog (BitVec 64) :=
.seq body771_14 body771_39

def body771_41 : Prog (BitVec 64) :=
.seq body771_13 body771_40

def body771_42 : Prog (BitVec 64) :=
.seq body771_12 body771_41

def body771_43 : Prog (BitVec 64) :=
.seq body771_11 body771_42

def body771_44 : Prog (BitVec 64) :=
.seq body771_10 body771_43

def body771_45 : Prog (BitVec 64) :=
.seq body771_9 body771_44

def body771_46 : Prog (BitVec 64) :=
.seq body771_8 body771_45

def body771_47 : Prog (BitVec 64) :=
.seq body771_7 body771_46

def body771_48 : Prog (BitVec 64) :=
.seq body771_6 body771_47

def body771_49 : Prog (BitVec 64) :=
.seq body771_5 body771_48

def body771_50 : Prog (BitVec 64) :=
.seq body771_4 body771_49

def body771_51 : Prog (BitVec 64) :=
.seq body771_3 body771_50

def body771_52 : Prog (BitVec 64) :=
.seq body771_2 body771_51

def body771_53 : Prog (BitVec 64) :=
.seq body771_1 body771_52

def body771_54 : Prog (BitVec 64) :=
.seq body771_0 body771_53

def body771_55 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]) body771_54

def body771_56 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64]) body771_55

def body771_57 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body771_56

def body771_58 : Prog (BitVec 64) :=
.dec ("ny") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) body771_57

def body771_59 : Prog (BitVec 64) :=
.dec ("nx") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body771_58

def body771_60 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body771_59

def body771_61 : Prog (BitVec 64) :=
.dec ("s2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body771_60

def body771_62 : Prog (BitVec 64) :=
.dec ("h") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body771_61

def body771_63 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body771_62

def body771_64 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body771_63

def body771_65 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body771_64

def body771_66 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 8#64]]) body771_65

def body771_67 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body771_66

def body771_68 : Prog (BitVec 64) :=
.seq body771_0 body771_1

def body771_69 : Prog (BitVec 64) :=
.seq body771_68 body771_2

def body771_70 : Prog (BitVec 64) :=
.seq body771_69 body771_3

def body771_71 : Prog (BitVec 64) :=
.seq body771_70 body771_4

def body771_72 : Prog (BitVec 64) :=
.seq body771_71 body771_5

def body771_73 : Prog (BitVec 64) :=
.seq body771_72 body771_6

def body771_74 : Prog (BitVec 64) :=
.seq body771_73 body771_7

def body771_75 : Prog (BitVec 64) :=
.seq body771_74 body771_8

def body771_76 : Prog (BitVec 64) :=
.seq body771_75 body771_9

def body771_77 : Prog (BitVec 64) :=
.seq body771_76 body771_10

def body771_78 : Prog (BitVec 64) :=
.seq body771_77 body771_11

def body771_79 : Prog (BitVec 64) :=
.seq body771_78 body771_12

def body771_80 : Prog (BitVec 64) :=
.seq body771_79 body771_13

def body771_81 : Prog (BitVec 64) :=
.seq body771_80 body771_14

def body771_82 : Prog (BitVec 64) :=
.seq body771_81 body771_15

def body771_83 : Prog (BitVec 64) :=
.seq body771_82 body771_16

def body771_84 : Prog (BitVec 64) :=
.seq body771_83 body771_17

def body771_85 : Prog (BitVec 64) :=
.seq body771_84 body771_7

def body771_86 : Prog (BitVec 64) :=
.seq body771_85 body771_7

def body771_87 : Prog (BitVec 64) :=
.seq body771_86 body771_7

def body771_88 : Prog (BitVec 64) :=
.seq body771_87 body771_18

def body771_89 : Prog (BitVec 64) :=
.seq body771_88 body771_19

def body771_90 : Prog (BitVec 64) :=
.seq body771_89 body771_7

def body771_91 : Prog (BitVec 64) :=
.seq body771_90 body771_7

def body771_92 : Prog (BitVec 64) :=
.seq body771_91 body771_7

def body771_93 : Prog (BitVec 64) :=
.seq body771_92 body771_20

def body771_94 : Prog (BitVec 64) :=
.seq body771_93 body771_21

def body771_95 : Prog (BitVec 64) :=
.seq body771_94 body771_22

def body771_96 : Prog (BitVec 64) :=
.seq body771_95 body771_23

def body771_97 : Prog (BitVec 64) :=
.seq body771_96 body771_24

def body771_98 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]) body771_97

def body771_99 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64]) body771_98

def body771_100 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body771_99

def body771_101 : Prog (BitVec 64) :=
.dec ("ny") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) body771_100

def body771_102 : Prog (BitVec 64) :=
.dec ("nx") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body771_101

def body771_103 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body771_102

def body771_104 : Prog (BitVec 64) :=
.dec ("s2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body771_103

def body771_105 : Prog (BitVec 64) :=
.dec ("h") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body771_104

def body771_106 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body771_105

def body771_107 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body771_106

def body771_108 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body771_107

def body771_109 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 8#64]]) body771_108

def body771_110 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body771_109

def originalData771 : Decl (BitVec 64) :=
.function { name := "g2_double", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body771_67, returnShape := (Flapjack.Shape.one) }
def simplifiedData771 : Decl (BitVec 64) :=
.function { name := "g2_double", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body771_110, returnShape := (Flapjack.Shape.one) }
def original771 := Pancake.PanLang.declToHOL originalData771
def simplified771 := Pancake.PanLang.declToHOL simplifiedData771
end InitECandidate.Proofs.FrontendStages.Declarations
