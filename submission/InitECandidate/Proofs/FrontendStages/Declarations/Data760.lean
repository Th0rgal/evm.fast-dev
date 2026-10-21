import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify744
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body760_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def body760_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body760_2 : Prog (BitVec 64) :=
.seq body760_0 body760_1

def body760_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body760_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i1") (Flapjack.Exp.const 1#64)) body760_2 body760_3

def body760_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def body760_6 : Prog (BitVec 64) :=
.seq body760_5 body760_1

def body760_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i2") (Flapjack.Exp.const 1#64)) body760_6 body760_3

def body760_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def body760_9 : Prog (BitVec 64) :=
.seq body760_8 body760_1

def body760_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ueq") (Flapjack.Exp.const 1#64)) body760_9 body760_3

def body760_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body760_12 : Prog (BitVec 64) :=
.seq body760_11 body760_1

def body760_13 : Prog (BitVec 64) :=
.seq body760_10 body760_12

def body760_14 : Prog (BitVec 64) :=
.decCall ("ueq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u2"]) body760_13

def body760_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "veq") (Flapjack.Exp.const 1#64)) body760_14 body760_3

def body760_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def body760_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "v3"]

def body760_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body760_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ny"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "ny"]

def body760_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v3", Flapjack.Exp.var Flapjack.VarKind.local "u2"]

def body760_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ny"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ny", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def body760_22 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "nx")

def body760_23 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ny")

def body760_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nz")

def body760_25 : Prog (BitVec 64) :=
.seq body760_24 body760_1

def body760_26 : Prog (BitVec 64) :=
.seq body760_23 body760_25

def body760_27 : Prog (BitVec 64) :=
.seq body760_22 body760_26

def body760_28 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v3", Flapjack.Exp.var Flapjack.VarKind.local "w"]) body760_27

def body760_29 : Prog (BitVec 64) :=
.seq body760_21 body760_28

def body760_30 : Prog (BitVec 64) :=
.seq body760_20 body760_29

def body760_31 : Prog (BitVec 64) :=
.seq body760_19 body760_30

def body760_32 : Prog (BitVec 64) :=
.decCall ("ny") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "vvv2", Flapjack.Exp.var Flapjack.VarKind.local "a"]) body760_31

def body760_33 : Prog (BitVec 64) :=
.decCall ("nx") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "a"]) body760_32

def body760_34 : Prog (BitVec 64) :=
.seq body760_18 body760_33

def body760_35 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "vvv2", Flapjack.Exp.var Flapjack.VarKind.local "vvv2"]) body760_34

def body760_36 : Prog (BitVec 64) :=
.seq body760_17 body760_35

def body760_37 : Prog (BitVec 64) :=
.seq body760_16 body760_36

def body760_38 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "u"]) body760_37

def body760_39 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_38

def body760_40 : Prog (BitVec 64) :=
.decCall ("v3") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "vv"]) body760_39

def body760_41 : Prog (BitVec 64) :=
.decCall ("vvv2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "vv", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) body760_40

def body760_42 : Prog (BitVec 64) :=
.decCall ("vv") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body760_41

def body760_43 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) body760_42

def body760_44 : Prog (BitVec 64) :=
.decCall ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u2"]) body760_43

def body760_45 : Prog (BitVec 64) :=
.seq body760_15 body760_44

def body760_46 : Prog (BitVec 64) :=
.decCall ("veq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) body760_45

def body760_47 : Prog (BitVec 64) :=
.decCall ("v2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_46

def body760_48 : Prog (BitVec 64) :=
.decCall ("v1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]) body760_47

def body760_49 : Prog (BitVec 64) :=
.decCall ("u2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_48

def body760_50 : Prog (BitVec 64) :=
.decCall ("u1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]) body760_49

def body760_51 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 48#64])) body760_50

def body760_52 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p2")) body760_51

def body760_53 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 48#64])) body760_52

def body760_54 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p1")) body760_53

def body760_55 : Prog (BitVec 64) :=
.seq body760_7 body760_54

def body760_56 : Prog (BitVec 64) :=
.decCall ("i2") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_55

def body760_57 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 96#64])) body760_56

def body760_58 : Prog (BitVec 64) :=
.seq body760_4 body760_57

def body760_59 : Prog (BitVec 64) :=
.decCall ("i1") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z1"]) body760_58

def body760_60 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 96#64])) body760_59

def body760_61 : Prog (BitVec 64) :=
.seq body760_10 body760_11

def body760_62 : Prog (BitVec 64) :=
.seq body760_61 body760_1

def body760_63 : Prog (BitVec 64) :=
.decCall ("ueq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u2"]) body760_62

def body760_64 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "veq") (Flapjack.Exp.const 1#64)) body760_63 body760_3

def body760_65 : Prog (BitVec 64) :=
.seq body760_16 body760_17

def body760_66 : Prog (BitVec 64) :=
.seq body760_19 body760_20

def body760_67 : Prog (BitVec 64) :=
.seq body760_66 body760_21

def body760_68 : Prog (BitVec 64) :=
.seq body760_22 body760_23

def body760_69 : Prog (BitVec 64) :=
.seq body760_68 body760_24

def body760_70 : Prog (BitVec 64) :=
.seq body760_69 body760_1

def body760_71 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v3", Flapjack.Exp.var Flapjack.VarKind.local "w"]) body760_70

def body760_72 : Prog (BitVec 64) :=
.seq body760_67 body760_71

def body760_73 : Prog (BitVec 64) :=
.decCall ("ny") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "vvv2", Flapjack.Exp.var Flapjack.VarKind.local "a"]) body760_72

def body760_74 : Prog (BitVec 64) :=
.decCall ("nx") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "a"]) body760_73

def body760_75 : Prog (BitVec 64) :=
.seq body760_18 body760_74

def body760_76 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "vvv2", Flapjack.Exp.var Flapjack.VarKind.local "vvv2"]) body760_75

def body760_77 : Prog (BitVec 64) :=
.seq body760_65 body760_76

def body760_78 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "u"]) body760_77

def body760_79 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_78

def body760_80 : Prog (BitVec 64) :=
.decCall ("v3") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "vv"]) body760_79

def body760_81 : Prog (BitVec 64) :=
.decCall ("vvv2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "vv", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) body760_80

def body760_82 : Prog (BitVec 64) :=
.decCall ("vv") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) body760_81

def body760_83 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) body760_82

def body760_84 : Prog (BitVec 64) :=
.decCall ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u2"]) body760_83

def body760_85 : Prog (BitVec 64) :=
.seq body760_64 body760_84

def body760_86 : Prog (BitVec 64) :=
.decCall ("veq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) body760_85

def body760_87 : Prog (BitVec 64) :=
.decCall ("v2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_86

def body760_88 : Prog (BitVec 64) :=
.decCall ("v1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]) body760_87

def body760_89 : Prog (BitVec 64) :=
.decCall ("u2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_88

def body760_90 : Prog (BitVec 64) :=
.decCall ("u1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]) body760_89

def body760_91 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 48#64])) body760_90

def body760_92 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p2")) body760_91

def body760_93 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 48#64])) body760_92

def body760_94 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p1")) body760_93

def body760_95 : Prog (BitVec 64) :=
.seq body760_7 body760_94

def body760_96 : Prog (BitVec 64) :=
.decCall ("i2") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body760_95

def body760_97 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 96#64])) body760_96

def body760_98 : Prog (BitVec 64) :=
.seq body760_4 body760_97

def body760_99 : Prog (BitVec 64) :=
.decCall ("i1") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z1"]) body760_98

def body760_100 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 96#64])) body760_99

def originalData760 : Decl (BitVec 64) :=
.function { name := "g1_add", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p1", Flapjack.Shape.one), ("p2", Flapjack.Shape.one)], body := body760_60, returnShape := (Flapjack.Shape.one) }
def simplifiedData760 : Decl (BitVec 64) :=
.function { name := "g1_add", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p1", Flapjack.Shape.one), ("p2", Flapjack.Shape.one)], body := body760_100, returnShape := (Flapjack.Shape.one) }
def original760 := Pancake.PanLang.declToHOL originalData760
def simplified760 := Pancake.PanLang.declToHOL simplifiedData760
end InitECandidate.Proofs.FrontendStages.Declarations
