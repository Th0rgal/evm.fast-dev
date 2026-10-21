import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify764
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body780_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "zsq", Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body780_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "ysq", Flapjack.Exp.var Flapjack.VarKind.local "qy"]

def body780_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "zsq",
    Flapjack.Exp.var Flapjack.VarKind.local "qx"]

def body780_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "qy",
    Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body780_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body780_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "ysq"]

def body780_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def body780_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def body780_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "rx"]

def body780_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t3", Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body780_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "t4", Flapjack.Exp.var Flapjack.VarKind.local "t3",
    Flapjack.Exp.var Flapjack.VarKind.local "t3"]

def body780_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "t4", Flapjack.Exp.var Flapjack.VarKind.local "t4",
    Flapjack.Exp.var Flapjack.VarKind.local "t4"]

def body780_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t5", Flapjack.Exp.var Flapjack.VarKind.local "t4",
    Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body780_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "ry"]

def body780_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "t6",
    Flapjack.Exp.var Flapjack.VarKind.local "ry"]

def body780_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t9", Flapjack.Exp.var Flapjack.VarKind.local "t6",
    Flapjack.Exp.var Flapjack.VarKind.local "qx"]

def body780_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t7", Flapjack.Exp.var Flapjack.VarKind.local "t4",
    Flapjack.Exp.var Flapjack.VarKind.local "rx"]

def body780_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "t6"]

def body780_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "t5"]

def body780_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "t7"]

def body780_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body780_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body780_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def body780_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "t3"]

def body780_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "t10", Flapjack.Exp.var Flapjack.VarKind.local "qy",
    Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body780_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t7", Flapjack.Exp.var Flapjack.VarKind.local "t7",
    Flapjack.Exp.var Flapjack.VarKind.local "t0"]

def body780_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t7", Flapjack.Exp.var Flapjack.VarKind.local "t7",
    Flapjack.Exp.var Flapjack.VarKind.local "t6"]

def body780_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "ry",
    Flapjack.Exp.var Flapjack.VarKind.local "t5"]

def body780_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body780_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ry", Flapjack.Exp.var Flapjack.VarKind.local "t7",
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body780_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "rx", Flapjack.Exp.var Flapjack.VarKind.local "t0"]

def body780_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t10", Flapjack.Exp.var Flapjack.VarKind.local "t10"]

def body780_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t10", Flapjack.Exp.var Flapjack.VarKind.local "t10",
    Flapjack.Exp.var Flapjack.VarKind.local "ysq"]

def body780_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body780_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t10", Flapjack.Exp.var Flapjack.VarKind.local "t10",
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def body780_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "t9", Flapjack.Exp.var Flapjack.VarKind.local "t9",
    Flapjack.Exp.var Flapjack.VarKind.local "t9"]

def body780_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t9", Flapjack.Exp.var Flapjack.VarKind.local "t10"]

def body780_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def body780_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "t6"]

def body780_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t6", Flapjack.Exp.var Flapjack.VarKind.local "t6"]

def body780_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body780_41 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body780_42 : Prog (BitVec 64) :=
.seq body780_40 body780_41

def body780_43 : Prog (BitVec 64) :=
.seq body780_39 body780_42

def body780_44 : Prog (BitVec 64) :=
.seq body780_38 body780_43

def body780_45 : Prog (BitVec 64) :=
.seq body780_37 body780_44

def body780_46 : Prog (BitVec 64) :=
.seq body780_36 body780_45

def body780_47 : Prog (BitVec 64) :=
.seq body780_35 body780_46

def body780_48 : Prog (BitVec 64) :=
.seq body780_34 body780_47

def body780_49 : Prog (BitVec 64) :=
.seq body780_33 body780_48

def body780_50 : Prog (BitVec 64) :=
.seq body780_32 body780_49

def body780_51 : Prog (BitVec 64) :=
.seq body780_31 body780_50

def body780_52 : Prog (BitVec 64) :=
.seq body780_30 body780_51

def body780_53 : Prog (BitVec 64) :=
.seq body780_29 body780_52

def body780_54 : Prog (BitVec 64) :=
.seq body780_28 body780_53

def body780_55 : Prog (BitVec 64) :=
.seq body780_27 body780_54

def body780_56 : Prog (BitVec 64) :=
.seq body780_26 body780_55

def body780_57 : Prog (BitVec 64) :=
.seq body780_25 body780_56

def body780_58 : Prog (BitVec 64) :=
.seq body780_24 body780_57

def body780_59 : Prog (BitVec 64) :=
.seq body780_23 body780_58

def body780_60 : Prog (BitVec 64) :=
.seq body780_22 body780_59

def body780_61 : Prog (BitVec 64) :=
.seq body780_21 body780_60

def body780_62 : Prog (BitVec 64) :=
.seq body780_20 body780_61

def body780_63 : Prog (BitVec 64) :=
.seq body780_19 body780_62

def body780_64 : Prog (BitVec 64) :=
.seq body780_19 body780_63

def body780_65 : Prog (BitVec 64) :=
.seq body780_18 body780_64

def body780_66 : Prog (BitVec 64) :=
.seq body780_17 body780_65

def body780_67 : Prog (BitVec 64) :=
.seq body780_16 body780_66

def body780_68 : Prog (BitVec 64) :=
.seq body780_15 body780_67

def body780_69 : Prog (BitVec 64) :=
.seq body780_14 body780_68

def body780_70 : Prog (BitVec 64) :=
.seq body780_13 body780_69

def body780_71 : Prog (BitVec 64) :=
.seq body780_12 body780_70

def body780_72 : Prog (BitVec 64) :=
.seq body780_11 body780_71

def body780_73 : Prog (BitVec 64) :=
.seq body780_10 body780_72

def body780_74 : Prog (BitVec 64) :=
.seq body780_9 body780_73

def body780_75 : Prog (BitVec 64) :=
.seq body780_8 body780_74

def body780_76 : Prog (BitVec 64) :=
.seq body780_7 body780_75

def body780_77 : Prog (BitVec 64) :=
.seq body780_6 body780_76

def body780_78 : Prog (BitVec 64) :=
.seq body780_5 body780_77

def body780_79 : Prog (BitVec 64) :=
.seq body780_4 body780_78

def body780_80 : Prog (BitVec 64) :=
.seq body780_3 body780_79

def body780_81 : Prog (BitVec 64) :=
.seq body780_2 body780_80

def body780_82 : Prog (BitVec 64) :=
.seq body780_1 body780_81

def body780_83 : Prog (BitVec 64) :=
.seq body780_0 body780_82

def body780_84 : Prog (BitVec 64) :=
.dec ("rz") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 192#64]) body780_83

def body780_85 : Prog (BitVec 64) :=
.dec ("ry") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 96#64]) body780_84

def body780_86 : Prog (BitVec 64) :=
.dec ("rx") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "rp") body780_85

def body780_87 : Prog (BitVec 64) :=
.dec ("t10") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1056#64]) body780_86

def body780_88 : Prog (BitVec 64) :=
.dec ("t9") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 960#64]) body780_87

def body780_89 : Prog (BitVec 64) :=
.dec ("t7") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 864#64]) body780_88

def body780_90 : Prog (BitVec 64) :=
.dec ("t6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 768#64]) body780_89

def body780_91 : Prog (BitVec 64) :=
.dec ("t5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) body780_90

def body780_92 : Prog (BitVec 64) :=
.dec ("t4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body780_91

def body780_93 : Prog (BitVec 64) :=
.dec ("t3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body780_92

def body780_94 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body780_93

def body780_95 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body780_94

def body780_96 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body780_95

def body780_97 : Prog (BitVec 64) :=
.dec ("ysq") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body780_96

def body780_98 : Prog (BitVec 64) :=
.dec ("zsq") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body780_97

def body780_99 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 12#64]]) body780_98

def body780_100 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body780_99

def body780_101 : Prog (BitVec 64) :=
.seq body780_0 body780_1

def body780_102 : Prog (BitVec 64) :=
.seq body780_101 body780_2

def body780_103 : Prog (BitVec 64) :=
.seq body780_102 body780_3

def body780_104 : Prog (BitVec 64) :=
.seq body780_103 body780_4

def body780_105 : Prog (BitVec 64) :=
.seq body780_104 body780_5

def body780_106 : Prog (BitVec 64) :=
.seq body780_105 body780_6

def body780_107 : Prog (BitVec 64) :=
.seq body780_106 body780_7

def body780_108 : Prog (BitVec 64) :=
.seq body780_107 body780_8

def body780_109 : Prog (BitVec 64) :=
.seq body780_108 body780_9

def body780_110 : Prog (BitVec 64) :=
.seq body780_109 body780_10

def body780_111 : Prog (BitVec 64) :=
.seq body780_110 body780_11

def body780_112 : Prog (BitVec 64) :=
.seq body780_111 body780_12

def body780_113 : Prog (BitVec 64) :=
.seq body780_112 body780_13

def body780_114 : Prog (BitVec 64) :=
.seq body780_113 body780_14

def body780_115 : Prog (BitVec 64) :=
.seq body780_114 body780_15

def body780_116 : Prog (BitVec 64) :=
.seq body780_115 body780_16

def body780_117 : Prog (BitVec 64) :=
.seq body780_116 body780_17

def body780_118 : Prog (BitVec 64) :=
.seq body780_117 body780_18

def body780_119 : Prog (BitVec 64) :=
.seq body780_118 body780_19

def body780_120 : Prog (BitVec 64) :=
.seq body780_119 body780_19

def body780_121 : Prog (BitVec 64) :=
.seq body780_120 body780_20

def body780_122 : Prog (BitVec 64) :=
.seq body780_121 body780_21

def body780_123 : Prog (BitVec 64) :=
.seq body780_122 body780_22

def body780_124 : Prog (BitVec 64) :=
.seq body780_123 body780_23

def body780_125 : Prog (BitVec 64) :=
.seq body780_124 body780_24

def body780_126 : Prog (BitVec 64) :=
.seq body780_125 body780_25

def body780_127 : Prog (BitVec 64) :=
.seq body780_126 body780_26

def body780_128 : Prog (BitVec 64) :=
.seq body780_127 body780_27

def body780_129 : Prog (BitVec 64) :=
.seq body780_128 body780_28

def body780_130 : Prog (BitVec 64) :=
.seq body780_129 body780_29

def body780_131 : Prog (BitVec 64) :=
.seq body780_130 body780_30

def body780_132 : Prog (BitVec 64) :=
.seq body780_131 body780_31

def body780_133 : Prog (BitVec 64) :=
.seq body780_132 body780_32

def body780_134 : Prog (BitVec 64) :=
.seq body780_133 body780_33

def body780_135 : Prog (BitVec 64) :=
.seq body780_134 body780_34

def body780_136 : Prog (BitVec 64) :=
.seq body780_135 body780_35

def body780_137 : Prog (BitVec 64) :=
.seq body780_136 body780_36

def body780_138 : Prog (BitVec 64) :=
.seq body780_137 body780_37

def body780_139 : Prog (BitVec 64) :=
.seq body780_138 body780_38

def body780_140 : Prog (BitVec 64) :=
.seq body780_139 body780_39

def body780_141 : Prog (BitVec 64) :=
.seq body780_140 body780_40

def body780_142 : Prog (BitVec 64) :=
.seq body780_141 body780_41

def body780_143 : Prog (BitVec 64) :=
.dec ("rz") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 192#64]) body780_142

def body780_144 : Prog (BitVec 64) :=
.dec ("ry") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 96#64]) body780_143

def body780_145 : Prog (BitVec 64) :=
.dec ("rx") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "rp") body780_144

def body780_146 : Prog (BitVec 64) :=
.dec ("t10") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1056#64]) body780_145

def body780_147 : Prog (BitVec 64) :=
.dec ("t9") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 960#64]) body780_146

def body780_148 : Prog (BitVec 64) :=
.dec ("t7") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 864#64]) body780_147

def body780_149 : Prog (BitVec 64) :=
.dec ("t6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 768#64]) body780_148

def body780_150 : Prog (BitVec 64) :=
.dec ("t5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) body780_149

def body780_151 : Prog (BitVec 64) :=
.dec ("t4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) body780_150

def body780_152 : Prog (BitVec 64) :=
.dec ("t3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) body780_151

def body780_153 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) body780_152

def body780_154 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) body780_153

def body780_155 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) body780_154

def body780_156 : Prog (BitVec 64) :=
.dec ("ysq") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) body780_155

def body780_157 : Prog (BitVec 64) :=
.dec ("zsq") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") body780_156

def body780_158 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 12#64]]) body780_157

def body780_159 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body780_158

def originalData780 : Decl (BitVec 64) :=
.function { name := "pair_addition_step", inline := false, exported := false, params := [("rp", Flapjack.Shape.one), ("qx", Flapjack.Shape.one), ("qy", Flapjack.Shape.one), ("co", Flapjack.Shape.one)], body := body780_100, returnShape := (Flapjack.Shape.one) }
def simplifiedData780 : Decl (BitVec 64) :=
.function { name := "pair_addition_step", inline := false, exported := false, params := [("rp", Flapjack.Shape.one), ("qx", Flapjack.Shape.one), ("qy", Flapjack.Shape.one), ("co", Flapjack.Shape.one)], body := body780_159, returnShape := (Flapjack.Shape.one) }
def original780 := Pancake.PanLang.declToHOL originalData780
def simplified780 := Pancake.PanLang.declToHOL simplifiedData780
end InitECandidate.Proofs.FrontendStages.Declarations
