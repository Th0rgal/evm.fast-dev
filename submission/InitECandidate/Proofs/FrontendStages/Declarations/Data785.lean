import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify769
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body785_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "temp"), none)) "bls_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "zt2", Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def body785_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "den"), none)) "bls_fp_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body785_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "temp"), none)) "bls_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "one"]

def body785_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "den"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "zc", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body785_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body785_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 1#64)) body785_3 body785_4

def body785_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "u"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def body785_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "den2"]

def body785_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "u"), none)) "bls_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body785_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body785_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "t3"]

def body785_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "c"]

def body785_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "num"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "num", Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def body785_13 : Prog (BitVec 64) :=
.seq body785_11 body785_12

def body785_14 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1856#64])) body785_13

def body785_15 : Prog (BitVec 64) :=
.seq body785_10 body785_14

def body785_16 : Prog (BitVec 64) :=
.decCall ("t3") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t"]) body785_15

def body785_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sq"))
  (Flapjack.Exp.const 0#64)) body785_16 body785_4

def body785_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body785_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "st_")
  (Flapjack.Exp.var Flapjack.VarKind.local "sy")) body785_18 body785_4

def body785_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def body785_21 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "num")

def body785_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y")

def body785_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "den")

def body785_24 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body785_25 : Prog (BitVec 64) :=
.seq body785_23 body785_24

def body785_26 : Prog (BitVec 64) :=
.seq body785_22 body785_25

def body785_27 : Prog (BitVec 64) :=
.seq body785_21 body785_26

def body785_28 : Prog (BitVec 64) :=
.seq body785_20 body785_27

def body785_29 : Prog (BitVec 64) :=
.seq body785_19 body785_28

def body785_30 : Prog (BitVec 64) :=
.decCall ("sy") (Flapjack.Shape.one) ("bls_fp_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body785_29

def body785_31 : Prog (BitVec 64) :=
.decCall ("st_") (Flapjack.Shape.one) ("bls_fp_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body785_30

def body785_32 : Prog (BitVec 64) :=
.seq body785_17 body785_31

def body785_33 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 6 (Flapjack.Exp.var Flapjack.VarKind.local "sq")]) body785_32

def body785_34 : Prog (BitVec 64) :=
.decCall ("sq") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("swu_sqrt_division_fp") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "v"]) body785_33

def body785_35 : Prog (BitVec 64) :=
.seq body785_8 body785_34

def body785_36 : Prog (BitVec 64) :=
.seq body785_9 body785_35

def body785_37 : Prog (BitVec 64) :=
.seq body785_8 body785_36

def body785_38 : Prog (BitVec 64) :=
.seq body785_7 body785_37

def body785_39 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "num"]) body785_38

def body785_40 : Prog (BitVec 64) :=
.seq body785_6 body785_39

def body785_41 : Prog (BitVec 64) :=
.decCall ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "num"]) body785_40

def body785_42 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "den2", Flapjack.Exp.var Flapjack.VarKind.local "den"]) body785_41

def body785_43 : Prog (BitVec 64) :=
.decCall ("den2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) body785_42

def body785_44 : Prog (BitVec 64) :=
.seq body785_5 body785_43

def body785_45 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) body785_44

def body785_46 : Prog (BitVec 64) :=
.decCall ("num") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "temp"]) body785_45

def body785_47 : Prog (BitVec 64) :=
.seq body785_2 body785_46

def body785_48 : Prog (BitVec 64) :=
.dec ("one") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
    Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
    Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64]) body785_47

def body785_49 : Prog (BitVec 64) :=
.seq body785_1 body785_48

def body785_50 : Prog (BitVec 64) :=
.decCall ("den") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "temp"]) body785_49

def body785_51 : Prog (BitVec 64) :=
.seq body785_0 body785_50

def body785_52 : Prog (BitVec 64) :=
.decCall ("temp") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "zt2"]) body785_51

def body785_53 : Prog (BitVec 64) :=
.decCall ("zt2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "zc", Flapjack.Exp.var Flapjack.VarKind.local "t2"]) body785_52

def body785_54 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body785_53

def body785_55 : Prog (BitVec 64) :=
.dec ("zc") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1808#64])) body785_54

def body785_56 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1760#64])) body785_55

def body785_57 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1712#64])) body785_56

def body785_58 : Prog (BitVec 64) :=
.seq body785_7 body785_8

def body785_59 : Prog (BitVec 64) :=
.seq body785_58 body785_9

def body785_60 : Prog (BitVec 64) :=
.seq body785_59 body785_8

def body785_61 : Prog (BitVec 64) :=
.seq body785_19 body785_20

def body785_62 : Prog (BitVec 64) :=
.seq body785_61 body785_21

def body785_63 : Prog (BitVec 64) :=
.seq body785_62 body785_22

def body785_64 : Prog (BitVec 64) :=
.seq body785_63 body785_23

def body785_65 : Prog (BitVec 64) :=
.seq body785_64 body785_24

def body785_66 : Prog (BitVec 64) :=
.decCall ("sy") (Flapjack.Shape.one) ("bls_fp_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body785_65

def body785_67 : Prog (BitVec 64) :=
.decCall ("st_") (Flapjack.Shape.one) ("bls_fp_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body785_66

def body785_68 : Prog (BitVec 64) :=
.seq body785_17 body785_67

def body785_69 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 6 (Flapjack.Exp.var Flapjack.VarKind.local "sq")]) body785_68

def body785_70 : Prog (BitVec 64) :=
.decCall ("sq") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("swu_sqrt_division_fp") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "v"]) body785_69

def body785_71 : Prog (BitVec 64) :=
.seq body785_60 body785_70

def body785_72 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "num"]) body785_71

def body785_73 : Prog (BitVec 64) :=
.seq body785_6 body785_72

def body785_74 : Prog (BitVec 64) :=
.decCall ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "num"]) body785_73

def body785_75 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "den2", Flapjack.Exp.var Flapjack.VarKind.local "den"]) body785_74

def body785_76 : Prog (BitVec 64) :=
.decCall ("den2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) body785_75

def body785_77 : Prog (BitVec 64) :=
.seq body785_5 body785_76

def body785_78 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) body785_77

def body785_79 : Prog (BitVec 64) :=
.decCall ("num") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "temp"]) body785_78

def body785_80 : Prog (BitVec 64) :=
.seq body785_2 body785_79

def body785_81 : Prog (BitVec 64) :=
.dec ("one") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
    Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
    Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64]) body785_80

def body785_82 : Prog (BitVec 64) :=
.seq body785_1 body785_81

def body785_83 : Prog (BitVec 64) :=
.decCall ("den") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "temp"]) body785_82

def body785_84 : Prog (BitVec 64) :=
.seq body785_0 body785_83

def body785_85 : Prog (BitVec 64) :=
.decCall ("temp") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "zt2"]) body785_84

def body785_86 : Prog (BitVec 64) :=
.decCall ("zt2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "zc", Flapjack.Exp.var Flapjack.VarKind.local "t2"]) body785_85

def body785_87 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body785_86

def body785_88 : Prog (BitVec 64) :=
.dec ("zc") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1808#64])) body785_87

def body785_89 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1760#64])) body785_88

def body785_90 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1712#64])) body785_89

def originalData785 : Decl (BitVec 64) :=
.function { name := "swu_g1", inline := false, exported := false, params := [("r", Flapjack.Shape.one),
  ("t",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body785_57, returnShape := (Flapjack.Shape.one) }
def simplifiedData785 : Decl (BitVec 64) :=
.function { name := "swu_g1", inline := false, exported := false, params := [("r", Flapjack.Shape.one),
  ("t",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body785_90, returnShape := (Flapjack.Shape.one) }
def original785 := Pancake.PanLang.declToHOL originalData785
def simplified785 := Pancake.PanLang.declToHOL simplifiedData785
end InitECandidate.Proofs.FrontendStages.Declarations
