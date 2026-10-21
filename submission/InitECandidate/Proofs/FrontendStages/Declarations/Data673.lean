import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify657
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body673_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn"]

def body673_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md"]

def body673_2 : Prog (BitVec 64) :=
.seq body673_0 body673_1

def body673_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn",
    Flapjack.Exp.var Flapjack.VarKind.local "y2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body673_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def body673_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn",
    Flapjack.Exp.var Flapjack.VarKind.local "mn", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body673_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body673_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def body673_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body673_9 : Prog (BitVec 64) :=
.seq body673_7 body673_8

def body673_10 : Prog (BitVec 64) :=
.seq body673_6 body673_9

def body673_11 : Prog (BitVec 64) :=
.seq body673_5 body673_10

def body673_12 : Prog (BitVec 64) :=
.seq body673_4 body673_11

def body673_13 : Prog (BitVec 64) :=
.seq body673_3 body673_12

def body673_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "P1")
  (Flapjack.Exp.var Flapjack.VarKind.local "P2")) body673_2 body673_13

def body673_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def body673_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn",
    Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.const 3#64]

def body673_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body673_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.const 2#64]

def body673_19 : Prog (BitVec 64) :=
.seq body673_17 body673_18

def body673_20 : Prog (BitVec 64) :=
.seq body673_16 body673_19

def body673_21 : Prog (BitVec 64) :=
.seq body673_15 body673_20

def body673_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "xt", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body673_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def body673_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "num", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body673_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def body673_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body673_27 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body673_28 : Prog (BitVec 64) :=
.seq body673_26 body673_27

def body673_29 : Prog (BitVec 64) :=
.seq body673_25 body673_28

def body673_30 : Prog (BitVec 64) :=
.seq body673_24 body673_29

def body673_31 : Prog (BitVec 64) :=
.seq body673_23 body673_30

def body673_32 : Prog (BitVec 64) :=
.seq body673_22 body673_31

def body673_33 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mnz") (Flapjack.Exp.const 1#64)) body673_21 body673_32

def body673_34 : Prog (BitVec 64) :=
.decCall ("mnz") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn"]) body673_33

def body673_35 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body673_36 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mdz") (Flapjack.Exp.const 1#64)) body673_34 body673_35

def body673_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "xt", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body673_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def body673_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body673_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "mn", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body673_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "yt", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body673_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def body673_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def body673_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body673_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body673_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def body673_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.var Flapjack.VarKind.local "den", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body673_48 : Prog (BitVec 64) :=
.seq body673_47 body673_28

def body673_49 : Prog (BitVec 64) :=
.seq body673_46 body673_48

def body673_50 : Prog (BitVec 64) :=
.seq body673_45 body673_49

def body673_51 : Prog (BitVec 64) :=
.seq body673_44 body673_50

def body673_52 : Prog (BitVec 64) :=
.seq body673_43 body673_51

def body673_53 : Prog (BitVec 64) :=
.seq body673_42 body673_52

def body673_54 : Prog (BitVec 64) :=
.seq body673_41 body673_53

def body673_55 : Prog (BitVec 64) :=
.seq body673_40 body673_54

def body673_56 : Prog (BitVec 64) :=
.seq body673_39 body673_55

def body673_57 : Prog (BitVec 64) :=
.seq body673_38 body673_56

def body673_58 : Prog (BitVec 64) :=
.seq body673_37 body673_57

def body673_59 : Prog (BitVec 64) :=
.seq body673_36 body673_58

def body673_60 : Prog (BitVec 64) :=
.decCall ("mdz") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md"]) body673_59

def body673_61 : Prog (BitVec 64) :=
.seq body673_14 body673_60

def body673_62 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_61

def body673_63 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_62

def body673_64 : Prog (BitVec 64) :=
.decCall ("md") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_63

def body673_65 : Prog (BitVec 64) :=
.decCall ("mn") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_64

def body673_66 : Prog (BitVec 64) :=
.dec ("zt") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body673_65

def body673_67 : Prog (BitVec 64) :=
.dec ("yt") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "T", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_66

def body673_68 : Prog (BitVec 64) :=
.dec ("xt") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "T") body673_67

def body673_69 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body673_68

def body673_70 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P2", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_69

def body673_71 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "P2") body673_70

def body673_72 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body673_71

def body673_73 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P1", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_72

def body673_74 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "P1") body673_73

def body673_75 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body673_74

def body673_76 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) body673_75

def body673_77 : Prog (BitVec 64) :=
.seq body673_3 body673_4

def body673_78 : Prog (BitVec 64) :=
.seq body673_77 body673_5

def body673_79 : Prog (BitVec 64) :=
.seq body673_78 body673_6

def body673_80 : Prog (BitVec 64) :=
.seq body673_79 body673_7

def body673_81 : Prog (BitVec 64) :=
.seq body673_80 body673_8

def body673_82 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "P1")
  (Flapjack.Exp.var Flapjack.VarKind.local "P2")) body673_2 body673_81

def body673_83 : Prog (BitVec 64) :=
.seq body673_15 body673_16

def body673_84 : Prog (BitVec 64) :=
.seq body673_83 body673_17

def body673_85 : Prog (BitVec 64) :=
.seq body673_84 body673_18

def body673_86 : Prog (BitVec 64) :=
.seq body673_22 body673_23

def body673_87 : Prog (BitVec 64) :=
.seq body673_86 body673_24

def body673_88 : Prog (BitVec 64) :=
.seq body673_87 body673_25

def body673_89 : Prog (BitVec 64) :=
.seq body673_88 body673_26

def body673_90 : Prog (BitVec 64) :=
.seq body673_89 body673_27

def body673_91 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mnz") (Flapjack.Exp.const 1#64)) body673_85 body673_90

def body673_92 : Prog (BitVec 64) :=
.decCall ("mnz") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn"]) body673_91

def body673_93 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mdz") (Flapjack.Exp.const 1#64)) body673_92 body673_35

def body673_94 : Prog (BitVec 64) :=
.seq body673_93 body673_37

def body673_95 : Prog (BitVec 64) :=
.seq body673_94 body673_38

def body673_96 : Prog (BitVec 64) :=
.seq body673_95 body673_39

def body673_97 : Prog (BitVec 64) :=
.seq body673_96 body673_40

def body673_98 : Prog (BitVec 64) :=
.seq body673_97 body673_41

def body673_99 : Prog (BitVec 64) :=
.seq body673_98 body673_42

def body673_100 : Prog (BitVec 64) :=
.seq body673_99 body673_43

def body673_101 : Prog (BitVec 64) :=
.seq body673_100 body673_44

def body673_102 : Prog (BitVec 64) :=
.seq body673_101 body673_45

def body673_103 : Prog (BitVec 64) :=
.seq body673_102 body673_46

def body673_104 : Prog (BitVec 64) :=
.seq body673_103 body673_47

def body673_105 : Prog (BitVec 64) :=
.seq body673_104 body673_26

def body673_106 : Prog (BitVec 64) :=
.seq body673_105 body673_27

def body673_107 : Prog (BitVec 64) :=
.decCall ("mdz") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md"]) body673_106

def body673_108 : Prog (BitVec 64) :=
.seq body673_82 body673_107

def body673_109 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_108

def body673_110 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_109

def body673_111 : Prog (BitVec 64) :=
.decCall ("md") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_110

def body673_112 : Prog (BitVec 64) :=
.decCall ("mn") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_111

def body673_113 : Prog (BitVec 64) :=
.dec ("zt") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body673_112

def body673_114 : Prog (BitVec 64) :=
.dec ("yt") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "T", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_113

def body673_115 : Prog (BitVec 64) :=
.dec ("xt") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "T") body673_114

def body673_116 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body673_115

def body673_117 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P2", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_116

def body673_118 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "P2") body673_117

def body673_119 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body673_118

def body673_120 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P1", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body673_119

def body673_121 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "P1") body673_120

def body673_122 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body673_121

def body673_123 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) body673_122

def originalData673 : Decl (BitVec 64) :=
.function { name := "ecp_linefunc", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("num", Flapjack.Shape.one), ("den", Flapjack.Shape.one), ("P1", Flapjack.Shape.one),
  ("P2", Flapjack.Shape.one), ("T", Flapjack.Shape.one)], body := body673_76, returnShape := (Flapjack.Shape.one) }
def simplifiedData673 : Decl (BitVec 64) :=
.function { name := "ecp_linefunc", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("num", Flapjack.Shape.one), ("den", Flapjack.Shape.one), ("P1", Flapjack.Shape.one),
  ("P2", Flapjack.Shape.one), ("T", Flapjack.Shape.one)], body := body673_123, returnShape := (Flapjack.Shape.one) }
def original673 := Pancake.PanLang.declToHOL originalData673
def simplified673 := Pancake.PanLang.declToHOL simplifiedData673
end InitECandidate.Proofs.FrontendStages.Declarations
