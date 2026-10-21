import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data790
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate774
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody790_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def globalBody790_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "zt2",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4736#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def globalBody790_2 : Prog (BitVec 64) :=
.seq globalBody790_0 globalBody790_1

def globalBody790_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def globalBody790_4 : Prog (BitVec 64) :=
.seq globalBody790_2 globalBody790_3

def globalBody790_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "zt2",
    Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def globalBody790_6 : Prog (BitVec 64) :=
.seq globalBody790_4 globalBody790_5

def globalBody790_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4544#64],
    Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def globalBody790_8 : Prog (BitVec 64) :=
.seq globalBody790_6 globalBody790_7

def globalBody790_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "den", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody790_10 : Prog (BitVec 64) :=
.seq globalBody790_8 globalBody790_9

def globalBody790_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody790_12 : Prog (BitVec 64) :=
.seq globalBody790_10 globalBody790_11

def globalBody790_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "temp",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody790_14 : Prog (BitVec 64) :=
.seq globalBody790_12 globalBody790_13

def globalBody790_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4640#64],
    Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def globalBody790_16 : Prog (BitVec 64) :=
.seq globalBody790_14 globalBody790_15

def globalBody790_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4736#64],
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4544#64]]

def globalBody790_18 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody790_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 1#64)) globalBody790_17 globalBody790_18

def globalBody790_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody790_21 : Prog (BitVec 64) :=
.seq globalBody790_19 globalBody790_20

def globalBody790_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody790_23 : Prog (BitVec 64) :=
.seq globalBody790_21 globalBody790_22

def globalBody790_24 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4544#64],
    Flapjack.Exp.var Flapjack.VarKind.local "num"]

def globalBody790_25 : Prog (BitVec 64) :=
.seq globalBody790_23 globalBody790_24

def globalBody790_26 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody790_27 : Prog (BitVec 64) :=
.seq globalBody790_25 globalBody790_26

def globalBody790_28 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def globalBody790_29 : Prog (BitVec 64) :=
.seq globalBody790_27 globalBody790_28

def globalBody790_30 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "num"]

def globalBody790_31 : Prog (BitVec 64) :=
.seq globalBody790_29 globalBody790_30

def globalBody790_32 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody790_33 : Prog (BitVec 64) :=
.seq globalBody790_31 globalBody790_32

def globalBody790_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4640#64],
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody790_35 : Prog (BitVec 64) :=
.seq globalBody790_33 globalBody790_34

def globalBody790_36 : Prog (BitVec 64) :=
.seq globalBody790_35 globalBody790_32

def globalBody790_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "cand", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "t"]

def globalBody790_38 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "cand", Flapjack.Exp.var Flapjack.VarKind.local "y",
    Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def globalBody790_39 : Prog (BitVec 64) :=
.seq globalBody790_37 globalBody790_38

def globalBody790_40 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def globalBody790_41 : Prog (BitVec 64) :=
.seq globalBody790_39 globalBody790_40

def globalBody790_42 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def globalBody790_43 : Prog (BitVec 64) :=
.seq globalBody790_41 globalBody790_42

def globalBody790_44 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody790_45 : Prog (BitVec 64) :=
.seq globalBody790_43 globalBody790_44

def globalBody790_46 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
        Flapjack.Exp.const 4832#64,
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 96#64]],
    Flapjack.Exp.var Flapjack.VarKind.local "cand"]

def globalBody790_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody790_48 : Prog (BitVec 64) :=
.seq globalBody790_46 globalBody790_47

def globalBody790_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "temp",
    Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody790_50 : Prog (BitVec 64) :=
.seq globalBody790_48 globalBody790_49

def globalBody790_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "temp",
    Flapjack.Exp.var Flapjack.VarKind.local "u1"]

def globalBody790_52 : Prog (BitVec 64) :=
.seq globalBody790_50 globalBody790_51

def globalBody790_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody790_54 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "success2" (Flapjack.Exp.const 1#64)

def globalBody790_55 : Prog (BitVec 64) :=
.seq globalBody790_53 globalBody790_54

def globalBody790_56 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 1#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "success")
        (Flapjack.Exp.const 0#64)),
    Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
      (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "success2")
        (Flapjack.Exp.const 0#64))]) globalBody790_55 globalBody790_18

def globalBody790_57 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def globalBody790_58 : Prog (BitVec 64) :=
.seq globalBody790_56 globalBody790_57

def globalBody790_59 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "temp"]) globalBody790_58

def globalBody790_60 : Prog (BitVec 64) :=
.seq globalBody790_52 globalBody790_59

def globalBody790_61 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 4#64)) globalBody790_60

def globalBody790_62 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "num", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def globalBody790_63 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "success") (Flapjack.Exp.const 0#64)) globalBody790_62 globalBody790_18

def globalBody790_64 : Prog (BitVec 64) :=
.seq globalBody790_61 globalBody790_63

def globalBody790_65 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "y"]

def globalBody790_66 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "st_")
  (Flapjack.Exp.var Flapjack.VarKind.local "sy")) globalBody790_65 globalBody790_18

def globalBody790_67 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "y",
    Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody790_68 : Prog (BitVec 64) :=
.seq globalBody790_66 globalBody790_67

def globalBody790_69 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def globalBody790_70 : Prog (BitVec 64) :=
.seq globalBody790_68 globalBody790_69

def globalBody790_71 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "y"]

def globalBody790_72 : Prog (BitVec 64) :=
.seq globalBody790_70 globalBody790_71

def globalBody790_73 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody790_74 : Prog (BitVec 64) :=
.seq globalBody790_72 globalBody790_73

def globalBody790_75 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody790_76 : Prog (BitVec 64) :=
.seq globalBody790_74 globalBody790_75

def globalBody790_77 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody790_78 : Prog (BitVec 64) :=
.seq globalBody790_76 globalBody790_77

def globalBody790_79 : Prog (BitVec 64) :=
.decCall ("sy") (Flapjack.Shape.one) ("fp2_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) globalBody790_78

def globalBody790_80 : Prog (BitVec 64) :=
.decCall ("st_") (Flapjack.Shape.one) ("fp2_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody790_79

def globalBody790_81 : Prog (BitVec 64) :=
.seq globalBody790_64 globalBody790_80

def globalBody790_82 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody790_81

def globalBody790_83 : Prog (BitVec 64) :=
.dec ("success2") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) globalBody790_82

def globalBody790_84 : Prog (BitVec 64) :=
.seq globalBody790_45 globalBody790_83

def globalBody790_85 : Prog (BitVec 64) :=
.decCall ("success") (Flapjack.Shape.one) ("swu_sqrt_division_fp2") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "u",
  Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody790_84

def globalBody790_86 : Prog (BitVec 64) :=
.seq globalBody790_36 globalBody790_85

def globalBody790_87 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("fp2_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) globalBody790_86

def globalBody790_88 : Prog (BitVec 64) :=
.seq globalBody790_16 globalBody790_87

def globalBody790_89 : Prog (BitVec 64) :=
.dec ("u1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 960#64]) globalBody790_88

def globalBody790_90 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 864#64]) globalBody790_89

def globalBody790_91 : Prog (BitVec 64) :=
.dec ("cand") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 768#64]) globalBody790_90

def globalBody790_92 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 672#64]) globalBody790_91

def globalBody790_93 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 576#64]) globalBody790_92

def globalBody790_94 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 480#64]) globalBody790_93

def globalBody790_95 : Prog (BitVec 64) :=
.dec ("num") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 384#64]) globalBody790_94

def globalBody790_96 : Prog (BitVec 64) :=
.dec ("den") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 288#64]) globalBody790_95

def globalBody790_97 : Prog (BitVec 64) :=
.dec ("temp") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 192#64]) globalBody790_96

def globalBody790_98 : Prog (BitVec 64) :=
.dec ("zt2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 96#64]) globalBody790_97

def globalBody790_99 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "s") globalBody790_98

def globalBody790_100 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 11#64]]) globalBody790_99

def globalBody790_101 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody790_100

def globalData790 : Decl (BitVec 64) :=
.function { name := "swu_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("t", Flapjack.Shape.one)], body := globalBody790_101, returnShape := (Flapjack.Shape.one) }
def globalOutput790 := Pancake.PanLang.declToHOL globalData790
end InitECandidate.Proofs.FrontendStages.Declarations
