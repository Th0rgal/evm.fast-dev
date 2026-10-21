import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify774
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body790_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body790_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "zt2",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4736#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def body790_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def body790_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "zt2",
    Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def body790_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4544#64],
    Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def body790_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "den", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body790_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body790_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "temp",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body790_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4640#64],
    Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def body790_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4736#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4544#64]]

def body790_10 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body790_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 1#64)) body790_9 body790_10

def body790_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body790_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body790_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4544#64],
    Flapjack.Exp.var Flapjack.VarKind.local "num"]

def body790_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body790_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def body790_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "num"]

def body790_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body790_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4640#64],
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body790_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "cand", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body790_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "cand", Flapjack.Exp.var Flapjack.VarKind.local "y",
    Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def body790_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def body790_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def body790_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body790_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 4832#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 96#64]],
    Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def body790_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body790_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "temp",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body790_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "temp",
    Flapjack.Exp.var Flapjack.VarKind.local "u1"]

def body790_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body790_30 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "success2" (Flapjack.Exp.const 1#64)

def body790_31 : Prog (BitVec 64) :=
.seq body790_29 body790_30

def body790_32 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "success")
        (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "success2")
        (Flapjack.Exp.const 0#64))]) body790_31 body790_10

def body790_33 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body790_34 : Prog (BitVec 64) :=
.seq body790_32 body790_33

def body790_35 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "temp"]) body790_34

def body790_36 : Prog (BitVec 64) :=
.seq body790_28 body790_35

def body790_37 : Prog (BitVec 64) :=
.seq body790_27 body790_36

def body790_38 : Prog (BitVec 64) :=
.seq body790_26 body790_37

def body790_39 : Prog (BitVec 64) :=
.seq body790_25 body790_38

def body790_40 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 4#64)) body790_39

def body790_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "num", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def body790_42 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "success") (Flapjack.Exp.const 0#64)) body790_41 body790_10

def body790_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body790_44 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "st_")
  (Flapjack.Exp.var Flapjack.VarKind.local "sy")) body790_43 body790_10

def body790_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "y",
    Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body790_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def body790_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body790_48 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body790_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body790_50 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body790_51 : Prog (BitVec 64) :=
.seq body790_49 body790_50

def body790_52 : Prog (BitVec 64) :=
.seq body790_48 body790_51

def body790_53 : Prog (BitVec 64) :=
.seq body790_47 body790_52

def body790_54 : Prog (BitVec 64) :=
.seq body790_46 body790_53

def body790_55 : Prog (BitVec 64) :=
.seq body790_45 body790_54

def body790_56 : Prog (BitVec 64) :=
.seq body790_44 body790_55

def body790_57 : Prog (BitVec 64) :=
.decCall ("sy") (Flapjack.Shape.one) ("fp2_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body790_56

def body790_58 : Prog (BitVec 64) :=
.decCall ("st_") (Flapjack.Shape.one) ("fp2_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body790_57

def body790_59 : Prog (BitVec 64) :=
.seq body790_42 body790_58

def body790_60 : Prog (BitVec 64) :=
.seq body790_40 body790_59

def body790_61 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body790_60

def body790_62 : Prog (BitVec 64) :=
.dec ("success2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body790_61

def body790_63 : Prog (BitVec 64) :=
.seq body790_24 body790_62

def body790_64 : Prog (BitVec 64) :=
.seq body790_23 body790_63

def body790_65 : Prog (BitVec 64) :=
.seq body790_22 body790_64

def body790_66 : Prog (BitVec 64) :=
.seq body790_21 body790_65

def body790_67 : Prog (BitVec 64) :=
.seq body790_20 body790_66

def body790_68 : Prog (BitVec 64) :=
.decCall ("success") (Flapjack.Shape.one) ("swu_sqrt_division_fp2") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "u",
  Flapjack.Exp.var Flapjack.VarKind.local "v"]) body790_67

def body790_69 : Prog (BitVec 64) :=
.seq body790_18 body790_68

def body790_70 : Prog (BitVec 64) :=
.seq body790_19 body790_69

def body790_71 : Prog (BitVec 64) :=
.seq body790_18 body790_70

def body790_72 : Prog (BitVec 64) :=
.seq body790_17 body790_71

def body790_73 : Prog (BitVec 64) :=
.seq body790_16 body790_72

def body790_74 : Prog (BitVec 64) :=
.seq body790_15 body790_73

def body790_75 : Prog (BitVec 64) :=
.seq body790_14 body790_74

def body790_76 : Prog (BitVec 64) :=
.seq body790_13 body790_75

def body790_77 : Prog (BitVec 64) :=
.seq body790_12 body790_76

def body790_78 : Prog (BitVec 64) :=
.seq body790_11 body790_77

def body790_79 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) body790_78

def body790_80 : Prog (BitVec 64) :=
.seq body790_8 body790_79

def body790_81 : Prog (BitVec 64) :=
.seq body790_7 body790_80

def body790_82 : Prog (BitVec 64) :=
.seq body790_6 body790_81

def body790_83 : Prog (BitVec 64) :=
.seq body790_5 body790_82

def body790_84 : Prog (BitVec 64) :=
.seq body790_4 body790_83

def body790_85 : Prog (BitVec 64) :=
.seq body790_3 body790_84

def body790_86 : Prog (BitVec 64) :=
.seq body790_2 body790_85

def body790_87 : Prog (BitVec 64) :=
.seq body790_1 body790_86

def body790_88 : Prog (BitVec 64) :=
.seq body790_0 body790_87

def body790_89 : Prog (BitVec 64) :=
.dec ("u1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 960#64]) body790_88

def body790_90 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 864#64]) body790_89

def body790_91 : Prog (BitVec 64) :=
.dec ("cand") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 768#64]) body790_90

def body790_92 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 672#64]) body790_91

def body790_93 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 576#64]) body790_92

def body790_94 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 480#64]) body790_93

def body790_95 : Prog (BitVec 64) :=
.dec ("num") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 384#64]) body790_94

def body790_96 : Prog (BitVec 64) :=
.dec ("den") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 288#64]) body790_95

def body790_97 : Prog (BitVec 64) :=
.dec ("temp") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 192#64]) body790_96

def body790_98 : Prog (BitVec 64) :=
.dec ("zt2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 96#64]) body790_97

def body790_99 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "s") body790_98

def body790_100 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 11#64]]) body790_99

def body790_101 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body790_100

def body790_102 : Prog (BitVec 64) :=
.seq body790_0 body790_1

def body790_103 : Prog (BitVec 64) :=
.seq body790_102 body790_2

def body790_104 : Prog (BitVec 64) :=
.seq body790_103 body790_3

def body790_105 : Prog (BitVec 64) :=
.seq body790_104 body790_4

def body790_106 : Prog (BitVec 64) :=
.seq body790_105 body790_5

def body790_107 : Prog (BitVec 64) :=
.seq body790_106 body790_6

def body790_108 : Prog (BitVec 64) :=
.seq body790_107 body790_7

def body790_109 : Prog (BitVec 64) :=
.seq body790_108 body790_8

def body790_110 : Prog (BitVec 64) :=
.seq body790_11 body790_12

def body790_111 : Prog (BitVec 64) :=
.seq body790_110 body790_13

def body790_112 : Prog (BitVec 64) :=
.seq body790_111 body790_14

def body790_113 : Prog (BitVec 64) :=
.seq body790_112 body790_15

def body790_114 : Prog (BitVec 64) :=
.seq body790_113 body790_16

def body790_115 : Prog (BitVec 64) :=
.seq body790_114 body790_17

def body790_116 : Prog (BitVec 64) :=
.seq body790_115 body790_18

def body790_117 : Prog (BitVec 64) :=
.seq body790_116 body790_19

def body790_118 : Prog (BitVec 64) :=
.seq body790_117 body790_18

def body790_119 : Prog (BitVec 64) :=
.seq body790_20 body790_21

def body790_120 : Prog (BitVec 64) :=
.seq body790_119 body790_22

def body790_121 : Prog (BitVec 64) :=
.seq body790_120 body790_23

def body790_122 : Prog (BitVec 64) :=
.seq body790_121 body790_24

def body790_123 : Prog (BitVec 64) :=
.seq body790_25 body790_26

def body790_124 : Prog (BitVec 64) :=
.seq body790_123 body790_27

def body790_125 : Prog (BitVec 64) :=
.seq body790_124 body790_28

def body790_126 : Prog (BitVec 64) :=
.seq body790_125 body790_35

def body790_127 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 4#64)) body790_126

def body790_128 : Prog (BitVec 64) :=
.seq body790_127 body790_42

def body790_129 : Prog (BitVec 64) :=
.seq body790_44 body790_45

def body790_130 : Prog (BitVec 64) :=
.seq body790_129 body790_46

def body790_131 : Prog (BitVec 64) :=
.seq body790_130 body790_47

def body790_132 : Prog (BitVec 64) :=
.seq body790_131 body790_48

def body790_133 : Prog (BitVec 64) :=
.seq body790_132 body790_49

def body790_134 : Prog (BitVec 64) :=
.seq body790_133 body790_50

def body790_135 : Prog (BitVec 64) :=
.decCall ("sy") (Flapjack.Shape.one) ("fp2_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body790_134

def body790_136 : Prog (BitVec 64) :=
.decCall ("st_") (Flapjack.Shape.one) ("fp2_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body790_135

def body790_137 : Prog (BitVec 64) :=
.seq body790_128 body790_136

def body790_138 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body790_137

def body790_139 : Prog (BitVec 64) :=
.dec ("success2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body790_138

def body790_140 : Prog (BitVec 64) :=
.seq body790_122 body790_139

def body790_141 : Prog (BitVec 64) :=
.decCall ("success") (Flapjack.Shape.one) ("swu_sqrt_division_fp2") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "u",
  Flapjack.Exp.var Flapjack.VarKind.local "v"]) body790_140

def body790_142 : Prog (BitVec 64) :=
.seq body790_118 body790_141

def body790_143 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) body790_142

def body790_144 : Prog (BitVec 64) :=
.seq body790_109 body790_143

def body790_145 : Prog (BitVec 64) :=
.dec ("u1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 960#64]) body790_144

def body790_146 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 864#64]) body790_145

def body790_147 : Prog (BitVec 64) :=
.dec ("cand") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 768#64]) body790_146

def body790_148 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 672#64]) body790_147

def body790_149 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 576#64]) body790_148

def body790_150 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 480#64]) body790_149

def body790_151 : Prog (BitVec 64) :=
.dec ("num") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 384#64]) body790_150

def body790_152 : Prog (BitVec 64) :=
.dec ("den") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 288#64]) body790_151

def body790_153 : Prog (BitVec 64) :=
.dec ("temp") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 192#64]) body790_152

def body790_154 : Prog (BitVec 64) :=
.dec ("zt2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 96#64]) body790_153

def body790_155 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "s") body790_154

def body790_156 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 11#64]]) body790_155

def body790_157 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body790_156

def originalData790 : Decl (BitVec 64) :=
.function { name := "swu_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("t", Flapjack.Shape.one)], body := body790_101, returnShape := (Flapjack.Shape.one) }
def simplifiedData790 : Decl (BitVec 64) :=
.function { name := "swu_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("t", Flapjack.Shape.one)], body := body790_157, returnShape := (Flapjack.Shape.one) }
def original790 := Pancake.PanLang.declToHOL originalData790
def simplified790 := Pancake.PanLang.declToHOL simplifiedData790
end InitECandidate.Proofs.FrontendStages.Declarations
