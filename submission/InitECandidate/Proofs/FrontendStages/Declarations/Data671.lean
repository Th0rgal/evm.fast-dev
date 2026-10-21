import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify655
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body671_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "p2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def body671_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body671_2 : Prog (BitVec 64) :=
.seq body671_0 body671_1

def body671_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body671_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z1z") (Flapjack.Exp.const 1#64)) body671_2 body671_3

def body671_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]

def body671_6 : Prog (BitVec 64) :=
.seq body671_5 body671_1

def body671_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z2z") (Flapjack.Exp.const 1#64)) body671_6 body671_3

def body671_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U1",
    Flapjack.Exp.var Flapjack.VarKind.local "y2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body671_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U2",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def body671_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V1",
    Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def body671_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V2",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def body671_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body671_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def body671_14 : Prog (BitVec 64) :=
.seq body671_13 body671_1

def body671_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ueq") (Flapjack.Exp.const 1#64)) body671_14 body671_3

def body671_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_set_inf"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body671_17 : Prog (BitVec 64) :=
.seq body671_16 body671_1

def body671_18 : Prog (BitVec 64) :=
.seq body671_15 body671_17

def body671_19 : Prog (BitVec 64) :=
.seq body671_12 body671_18

def body671_20 : Prog (BitVec 64) :=
.decCall ("ueq") (Flapjack.Shape.one) ("fe_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U1",
  Flapjack.Exp.var Flapjack.VarKind.local "U2"]) body671_19

def body671_21 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "veq") (Flapjack.Exp.const 1#64)) body671_20 body671_3

def body671_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U",
    Flapjack.Exp.var Flapjack.VarKind.local "U1", Flapjack.Exp.var Flapjack.VarKind.local "U2"]

def body671_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "V1", Flapjack.Exp.var Flapjack.VarKind.local "V2"]

def body671_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "Vsq",
    Flapjack.Exp.var Flapjack.VarKind.local "V"]

def body671_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "VsqV2",
    Flapjack.Exp.var Flapjack.VarKind.local "Vsq", Flapjack.Exp.var Flapjack.VarKind.local "V2"]

def body671_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "Vcu",
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "Vsq"]

def body671_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def body671_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "U"]

def body671_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "A", Flapjack.Exp.var Flapjack.VarKind.local "W"]

def body671_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "A", Flapjack.Exp.var Flapjack.VarKind.local "Vcu"]

def body671_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.var Flapjack.VarKind.local "VsqV2", Flapjack.Exp.const 2#64]

def body671_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "A",
    Flapjack.Exp.var Flapjack.VarKind.local "A", Flapjack.Exp.var Flapjack.VarKind.local "T"]

def body671_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "A"]

def body671_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "VsqV2", Flapjack.Exp.var Flapjack.VarKind.local "A"]

def body671_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "U", Flapjack.Exp.var Flapjack.VarKind.local "V"]

def body671_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U1",
    Flapjack.Exp.var Flapjack.VarKind.local "Vcu", Flapjack.Exp.var Flapjack.VarKind.local "U2"]

def body671_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V",
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "U1"]

def body671_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "Vcu", Flapjack.Exp.var Flapjack.VarKind.local "W"]

def body671_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def body671_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "esz"],
    Flapjack.Exp.var Flapjack.VarKind.local "V", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def body671_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "W", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def body671_42 : Prog (BitVec 64) :=
.seq body671_12 body671_1

def body671_43 : Prog (BitVec 64) :=
.seq body671_41 body671_42

def body671_44 : Prog (BitVec 64) :=
.seq body671_40 body671_43

def body671_45 : Prog (BitVec 64) :=
.seq body671_39 body671_44

def body671_46 : Prog (BitVec 64) :=
.seq body671_38 body671_45

def body671_47 : Prog (BitVec 64) :=
.seq body671_37 body671_46

def body671_48 : Prog (BitVec 64) :=
.seq body671_36 body671_47

def body671_49 : Prog (BitVec 64) :=
.seq body671_35 body671_48

def body671_50 : Prog (BitVec 64) :=
.seq body671_34 body671_49

def body671_51 : Prog (BitVec 64) :=
.seq body671_33 body671_50

def body671_52 : Prog (BitVec 64) :=
.seq body671_32 body671_51

def body671_53 : Prog (BitVec 64) :=
.seq body671_31 body671_52

def body671_54 : Prog (BitVec 64) :=
.seq body671_30 body671_53

def body671_55 : Prog (BitVec 64) :=
.seq body671_29 body671_54

def body671_56 : Prog (BitVec 64) :=
.seq body671_28 body671_55

def body671_57 : Prog (BitVec 64) :=
.seq body671_27 body671_56

def body671_58 : Prog (BitVec 64) :=
.seq body671_26 body671_57

def body671_59 : Prog (BitVec 64) :=
.seq body671_25 body671_58

def body671_60 : Prog (BitVec 64) :=
.seq body671_24 body671_59

def body671_61 : Prog (BitVec 64) :=
.seq body671_23 body671_60

def body671_62 : Prog (BitVec 64) :=
.seq body671_22 body671_61

def body671_63 : Prog (BitVec 64) :=
.decCall ("T") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_62

def body671_64 : Prog (BitVec 64) :=
.decCall ("A") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_63

def body671_65 : Prog (BitVec 64) :=
.decCall ("W") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_64

def body671_66 : Prog (BitVec 64) :=
.decCall ("Vcu") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_65

def body671_67 : Prog (BitVec 64) :=
.decCall ("VsqV2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_66

def body671_68 : Prog (BitVec 64) :=
.decCall ("Vsq") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_67

def body671_69 : Prog (BitVec 64) :=
.decCall ("V") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_68

def body671_70 : Prog (BitVec 64) :=
.decCall ("U") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_69

def body671_71 : Prog (BitVec 64) :=
.seq body671_21 body671_70

def body671_72 : Prog (BitVec 64) :=
.decCall ("veq") (Flapjack.Shape.one) ("fe_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V1",
  Flapjack.Exp.var Flapjack.VarKind.local "V2"]) body671_71

def body671_73 : Prog (BitVec 64) :=
.seq body671_11 body671_72

def body671_74 : Prog (BitVec 64) :=
.seq body671_10 body671_73

def body671_75 : Prog (BitVec 64) :=
.seq body671_9 body671_74

def body671_76 : Prog (BitVec 64) :=
.seq body671_8 body671_75

def body671_77 : Prog (BitVec 64) :=
.decCall ("V2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_76

def body671_78 : Prog (BitVec 64) :=
.decCall ("V1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_77

def body671_79 : Prog (BitVec 64) :=
.decCall ("U2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_78

def body671_80 : Prog (BitVec 64) :=
.decCall ("U1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_79

def body671_81 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body671_80

def body671_82 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_81

def body671_83 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p2") body671_82

def body671_84 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body671_83

def body671_85 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_84

def body671_86 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p1") body671_85

def body671_87 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body671_86

def body671_88 : Prog (BitVec 64) :=
.seq body671_7 body671_87

def body671_89 : Prog (BitVec 64) :=
.decCall ("z2z") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p2",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]) body671_88

def body671_90 : Prog (BitVec 64) :=
.seq body671_4 body671_89

def body671_91 : Prog (BitVec 64) :=
.decCall ("z1z") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]) body671_90

def body671_92 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) body671_91

def body671_93 : Prog (BitVec 64) :=
.seq body671_8 body671_9

def body671_94 : Prog (BitVec 64) :=
.seq body671_93 body671_10

def body671_95 : Prog (BitVec 64) :=
.seq body671_94 body671_11

def body671_96 : Prog (BitVec 64) :=
.seq body671_12 body671_15

def body671_97 : Prog (BitVec 64) :=
.seq body671_96 body671_16

def body671_98 : Prog (BitVec 64) :=
.seq body671_97 body671_1

def body671_99 : Prog (BitVec 64) :=
.decCall ("ueq") (Flapjack.Shape.one) ("fe_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "U1",
  Flapjack.Exp.var Flapjack.VarKind.local "U2"]) body671_98

def body671_100 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "veq") (Flapjack.Exp.const 1#64)) body671_99 body671_3

def body671_101 : Prog (BitVec 64) :=
.seq body671_22 body671_23

def body671_102 : Prog (BitVec 64) :=
.seq body671_101 body671_24

def body671_103 : Prog (BitVec 64) :=
.seq body671_102 body671_25

def body671_104 : Prog (BitVec 64) :=
.seq body671_103 body671_26

def body671_105 : Prog (BitVec 64) :=
.seq body671_104 body671_27

def body671_106 : Prog (BitVec 64) :=
.seq body671_105 body671_28

def body671_107 : Prog (BitVec 64) :=
.seq body671_106 body671_29

def body671_108 : Prog (BitVec 64) :=
.seq body671_107 body671_30

def body671_109 : Prog (BitVec 64) :=
.seq body671_108 body671_31

def body671_110 : Prog (BitVec 64) :=
.seq body671_109 body671_32

def body671_111 : Prog (BitVec 64) :=
.seq body671_110 body671_33

def body671_112 : Prog (BitVec 64) :=
.seq body671_111 body671_34

def body671_113 : Prog (BitVec 64) :=
.seq body671_112 body671_35

def body671_114 : Prog (BitVec 64) :=
.seq body671_113 body671_36

def body671_115 : Prog (BitVec 64) :=
.seq body671_114 body671_37

def body671_116 : Prog (BitVec 64) :=
.seq body671_115 body671_38

def body671_117 : Prog (BitVec 64) :=
.seq body671_116 body671_39

def body671_118 : Prog (BitVec 64) :=
.seq body671_117 body671_40

def body671_119 : Prog (BitVec 64) :=
.seq body671_118 body671_41

def body671_120 : Prog (BitVec 64) :=
.seq body671_119 body671_12

def body671_121 : Prog (BitVec 64) :=
.seq body671_120 body671_1

def body671_122 : Prog (BitVec 64) :=
.decCall ("T") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_121

def body671_123 : Prog (BitVec 64) :=
.decCall ("A") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_122

def body671_124 : Prog (BitVec 64) :=
.decCall ("W") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_123

def body671_125 : Prog (BitVec 64) :=
.decCall ("Vcu") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_124

def body671_126 : Prog (BitVec 64) :=
.decCall ("VsqV2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_125

def body671_127 : Prog (BitVec 64) :=
.decCall ("Vsq") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_126

def body671_128 : Prog (BitVec 64) :=
.decCall ("V") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_127

def body671_129 : Prog (BitVec 64) :=
.decCall ("U") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_128

def body671_130 : Prog (BitVec 64) :=
.seq body671_100 body671_129

def body671_131 : Prog (BitVec 64) :=
.decCall ("veq") (Flapjack.Shape.one) ("fe_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "V1",
  Flapjack.Exp.var Flapjack.VarKind.local "V2"]) body671_130

def body671_132 : Prog (BitVec 64) :=
.seq body671_95 body671_131

def body671_133 : Prog (BitVec 64) :=
.decCall ("V2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_132

def body671_134 : Prog (BitVec 64) :=
.decCall ("V1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_133

def body671_135 : Prog (BitVec 64) :=
.decCall ("U2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_134

def body671_136 : Prog (BitVec 64) :=
.decCall ("U1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_135

def body671_137 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body671_136

def body671_138 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_137

def body671_139 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p2") body671_138

def body671_140 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) body671_139

def body671_141 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) body671_140

def body671_142 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p1") body671_141

def body671_143 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body671_142

def body671_144 : Prog (BitVec 64) :=
.seq body671_7 body671_143

def body671_145 : Prog (BitVec 64) :=
.decCall ("z2z") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p2",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]) body671_144

def body671_146 : Prog (BitVec 64) :=
.seq body671_4 body671_145

def body671_147 : Prog (BitVec 64) :=
.decCall ("z1z") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld",
  Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "p1",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]]) body671_146

def body671_148 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) body671_147

def originalData671 : Decl (BitVec 64) :=
.function { name := "ecp_add", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("p1", Flapjack.Shape.one), ("p2", Flapjack.Shape.one)], body := body671_92, returnShape := (Flapjack.Shape.one) }
def simplifiedData671 : Decl (BitVec 64) :=
.function { name := "ecp_add", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("p1", Flapjack.Shape.one), ("p2", Flapjack.Shape.one)], body := body671_148, returnShape := (Flapjack.Shape.one) }
def original671 := Pancake.PanLang.declToHOL originalData671
def simplified671 := Pancake.PanLang.declToHOL simplifiedData671
end InitECandidate.Proofs.FrontendStages.Declarations
