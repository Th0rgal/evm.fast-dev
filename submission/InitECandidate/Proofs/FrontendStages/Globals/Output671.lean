import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data671
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate655
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody671_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "p2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def globalBody671_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody671_2 : Prog (BitVec 64) :=
.seq globalBody671_0 globalBody671_1

def globalBody671_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody671_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z1z") (Flapjack.Exp.const 1#64)) globalBody671_2 globalBody671_3

def globalBody671_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def globalBody671_6 : Prog (BitVec 64) :=
.seq globalBody671_5 globalBody671_1

def globalBody671_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z2z") (Flapjack.Exp.const 1#64)) globalBody671_6 globalBody671_3

def globalBody671_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U1",
    Flapjack.Exp.var Flapjack.VarKind.local "y2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody671_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U2",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def globalBody671_10 : Prog (BitVec 64) :=
.seq globalBody671_8 globalBody671_9

def globalBody671_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V1",
    Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody671_12 : Prog (BitVec 64) :=
.seq globalBody671_10 globalBody671_11

def globalBody671_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V2",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def globalBody671_14 : Prog (BitVec 64) :=
.seq globalBody671_12 globalBody671_13

def globalBody671_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody671_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def globalBody671_17 : Prog (BitVec 64) :=
.seq globalBody671_16 globalBody671_1

def globalBody671_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ueq") (Flapjack.Exp.const 1#64)) globalBody671_17 globalBody671_3

def globalBody671_19 : Prog (BitVec 64) :=
.seq globalBody671_15 globalBody671_18

def globalBody671_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_set_inf"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody671_21 : Prog (BitVec 64) :=
.seq globalBody671_19 globalBody671_20

def globalBody671_22 : Prog (BitVec 64) :=
.seq globalBody671_21 globalBody671_1

def globalBody671_23 : Prog (BitVec 64) :=
.decCall ("ueq") (Flapjack.Shape.one) ("fe_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U1",
  Flapjack.Exp.var Flapjack.VarKind.local "U2"]) globalBody671_22

def globalBody671_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "veq") (Flapjack.Exp.const 1#64)) globalBody671_23 globalBody671_3

def globalBody671_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U",
    Flapjack.Exp.var Flapjack.VarKind.local "U1", Flapjack.Exp.var Flapjack.VarKind.local "U2"]

def globalBody671_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "V1", Flapjack.Exp.var Flapjack.VarKind.local "V2"]

def globalBody671_27 : Prog (BitVec 64) :=
.seq globalBody671_25 globalBody671_26

def globalBody671_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "Vsq",
    Flapjack.Exp.var Flapjack.VarKind.local "V"]

def globalBody671_29 : Prog (BitVec 64) :=
.seq globalBody671_27 globalBody671_28

def globalBody671_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "VsqV2",
    Flapjack.Exp.var Flapjack.VarKind.local "Vsq", Flapjack.Exp.var Flapjack.VarKind.local "V2"]

def globalBody671_31 : Prog (BitVec 64) :=
.seq globalBody671_29 globalBody671_30

def globalBody671_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "Vcu",
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "Vsq"]

def globalBody671_33 : Prog (BitVec 64) :=
.seq globalBody671_31 globalBody671_32

def globalBody671_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def globalBody671_35 : Prog (BitVec 64) :=
.seq globalBody671_33 globalBody671_34

def globalBody671_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "U"]

def globalBody671_37 : Prog (BitVec 64) :=
.seq globalBody671_35 globalBody671_36

def globalBody671_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "A", Flapjack.Exp.var Flapjack.VarKind.local "W"]

def globalBody671_39 : Prog (BitVec 64) :=
.seq globalBody671_37 globalBody671_38

def globalBody671_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "A", Flapjack.Exp.var Flapjack.VarKind.local "Vcu"]

def globalBody671_41 : Prog (BitVec 64) :=
.seq globalBody671_39 globalBody671_40

def globalBody671_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.var Flapjack.VarKind.local "VsqV2", Flapjack.Exp.const 2#64]

def globalBody671_43 : Prog (BitVec 64) :=
.seq globalBody671_41 globalBody671_42

def globalBody671_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "A", Flapjack.Exp.var Flapjack.VarKind.local "T"]

def globalBody671_45 : Prog (BitVec 64) :=
.seq globalBody671_43 globalBody671_44

def globalBody671_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "A"]

def globalBody671_47 : Prog (BitVec 64) :=
.seq globalBody671_45 globalBody671_46

def globalBody671_48 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "VsqV2", Flapjack.Exp.var Flapjack.VarKind.local "A"]

def globalBody671_49 : Prog (BitVec 64) :=
.seq globalBody671_47 globalBody671_48

def globalBody671_50 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "U", Flapjack.Exp.var Flapjack.VarKind.local "V"]

def globalBody671_51 : Prog (BitVec 64) :=
.seq globalBody671_49 globalBody671_50

def globalBody671_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U1",
    Flapjack.Exp.var Flapjack.VarKind.local "Vcu", Flapjack.Exp.var Flapjack.VarKind.local "U2"]

def globalBody671_53 : Prog (BitVec 64) :=
.seq globalBody671_51 globalBody671_52

def globalBody671_54 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "U1"]

def globalBody671_55 : Prog (BitVec 64) :=
.seq globalBody671_53 globalBody671_54

def globalBody671_56 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "Vcu", Flapjack.Exp.var Flapjack.VarKind.local "W"]

def globalBody671_57 : Prog (BitVec 64) :=
.seq globalBody671_55 globalBody671_56

def globalBody671_58 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody671_59 : Prog (BitVec 64) :=
.seq globalBody671_57 globalBody671_58

def globalBody671_60 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "esz"],
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody671_61 : Prog (BitVec 64) :=
.seq globalBody671_59 globalBody671_60

def globalBody671_62 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "W", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody671_63 : Prog (BitVec 64) :=
.seq globalBody671_61 globalBody671_62

def globalBody671_64 : Prog (BitVec 64) :=
.seq globalBody671_63 globalBody671_15

def globalBody671_65 : Prog (BitVec 64) :=
.seq globalBody671_64 globalBody671_1

def globalBody671_66 : Prog (BitVec 64) :=
.decCall ("T") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_65

def globalBody671_67 : Prog (BitVec 64) :=
.decCall ("A") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_66

def globalBody671_68 : Prog (BitVec 64) :=
.decCall ("W") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_67

def globalBody671_69 : Prog (BitVec 64) :=
.decCall ("Vcu") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_68

def globalBody671_70 : Prog (BitVec 64) :=
.decCall ("VsqV2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_69

def globalBody671_71 : Prog (BitVec 64) :=
.decCall ("Vsq") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_70

def globalBody671_72 : Prog (BitVec 64) :=
.decCall ("V") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_71

def globalBody671_73 : Prog (BitVec 64) :=
.decCall ("U") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_72

def globalBody671_74 : Prog (BitVec 64) :=
.seq globalBody671_24 globalBody671_73

def globalBody671_75 : Prog (BitVec 64) :=
.decCall ("veq") (Flapjack.Shape.one) ("fe_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V1",
  Flapjack.Exp.var Flapjack.VarKind.local "V2"]) globalBody671_74

def globalBody671_76 : Prog (BitVec 64) :=
.seq globalBody671_14 globalBody671_75

def globalBody671_77 : Prog (BitVec 64) :=
.decCall ("V2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_76

def globalBody671_78 : Prog (BitVec 64) :=
.decCall ("V1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_77

def globalBody671_79 : Prog (BitVec 64) :=
.decCall ("U2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_78

def globalBody671_80 : Prog (BitVec 64) :=
.decCall ("U1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_79

def globalBody671_81 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody671_80

def globalBody671_82 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_81

def globalBody671_83 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p2") globalBody671_82

def globalBody671_84 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody671_83

def globalBody671_85 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody671_84

def globalBody671_86 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p1") globalBody671_85

def globalBody671_87 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody671_86

def globalBody671_88 : Prog (BitVec 64) :=
.seq globalBody671_7 globalBody671_87

def globalBody671_89 : Prog (BitVec 64) :=
.decCall ("z2z") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p2",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]) globalBody671_88

def globalBody671_90 : Prog (BitVec 64) :=
.seq globalBody671_4 globalBody671_89

def globalBody671_91 : Prog (BitVec 64) :=
.decCall ("z1z") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]) globalBody671_90

def globalBody671_92 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) globalBody671_91

def globalData671 : Decl (BitVec 64) :=
.function { name := "ecp_add", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("p1", Flapjack.Shape.one), ("p2", Flapjack.Shape.one)], body := globalBody671_92, returnShape := (Flapjack.Shape.one) }
def globalOutput671 := Pancake.PanLang.declToHOL globalData671
end InitECandidate.Proofs.FrontendStages.Declarations
