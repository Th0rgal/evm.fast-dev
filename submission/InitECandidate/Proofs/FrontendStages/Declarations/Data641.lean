import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify625
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body641_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body641_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body641_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rz") (Flapjack.Exp.const 1#64)) body641_0 body641_1

def body641_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rlt") (Flapjack.Exp.const 0#64)) body641_0 body641_1

def body641_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sz") (Flapjack.Exp.const 1#64)) body641_0 body641_1

def body641_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "slt") (Flapjack.Exp.const 0#64)) body641_0 body641_1

def body641_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "xlt") (Flapjack.Exp.const 0#64)) body641_0 body641_1

def body641_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ylt") (Flapjack.Exp.const 0#64)) body641_0 body641_1

def body641_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qx"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qx"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "qx"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "qx"),
      Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "qy"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "qy"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "qy"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "qy")])
  (Flapjack.Exp.const 0#64)) body641_0 body641_1

def body641_9 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "onc") (Flapjack.Exp.const 0#64)) body641_0 body641_1

def body641_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "e"), none)) "u256_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "e",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
        Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]

def body641_11 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "elt") (Flapjack.Exp.const 0#64)) body641_10 body641_1

def body641_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_ec_mul2"
  [Flapjack.Exp.var Flapjack.VarKind.local "pr", Flapjack.Exp.var Flapjack.VarKind.local "u1",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 17627433388654248598#64, Flapjack.Exp.const 8575836109218198432#64,
        Flapjack.Exp.const 17923454489921339634#64, Flapjack.Exp.const 7716867327612699207#64],
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 14678990851816772085#64, Flapjack.Exp.const 3156516839386865358#64,
        Flapjack.Exp.const 10297457778147434006#64, Flapjack.Exp.const 5756518291402817435#64],
    Flapjack.Exp.var Flapjack.VarKind.local "u2", Flapjack.Exp.var Flapjack.VarKind.local "qx",
    Flapjack.Exp.var Flapjack.VarKind.local "qy"]

def body641_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body641_14 : Prog (BitVec 64) :=
.seq body641_13 body641_0

def body641_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "zz") (Flapjack.Exp.const 1#64)) body641_14 body641_1

def body641_16 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body641_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 1#64)) body641_16 body641_1

def body641_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "rn"))
  (Flapjack.Exp.const 1#64)) body641_0 body641_1

def body641_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rnlt") (Flapjack.Exp.const 0#64)) body641_0 body641_1

def body641_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "p256_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "rn4", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def body641_21 : Prog (BitVec 64) :=
Flapjack.Prog.call none "u256_eq"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body641_22 : Prog (BitVec 64) :=
.seq body641_20 body641_21

def body641_23 : Prog (BitVec 64) :=
.seq body641_19 body641_22

def body641_24 : Prog (BitVec 64) :=
.decCall ("rnlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "rn4",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) body641_23

def body641_25 : Prog (BitVec 64) :=
.dec ("rn4") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "rn")]) body641_24

def body641_26 : Prog (BitVec 64) :=
.seq body641_18 body641_25

def body641_27 : Prog (BitVec 64) :=
.decCall ("rn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_26

def body641_28 : Prog (BitVec 64) :=
.seq body641_17 body641_27

def body641_29 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "x"]) body641_28

def body641_30 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body641_29

def body641_31 : Prog (BitVec 64) :=
.seq body641_13 body641_30

def body641_32 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pr")) body641_31

def body641_33 : Prog (BitVec 64) :=
.decCall ("z2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) body641_32

def body641_34 : Prog (BitVec 64) :=
.seq body641_15 body641_33

def body641_35 : Prog (BitVec 64) :=
.decCall ("zz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) body641_34

def body641_36 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pr", Flapjack.Exp.const 64#64])) body641_35

def body641_37 : Prog (BitVec 64) :=
.seq body641_12 body641_36

def body641_38 : Prog (BitVec 64) :=
.decCall ("pr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body641_37

def body641_39 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body641_38

def body641_40 : Prog (BitVec 64) :=
.decCall ("u2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mulmod") ([Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "sinv",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_39

def body641_41 : Prog (BitVec 64) :=
.decCall ("u1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mulmod") ([Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.var Flapjack.VarKind.local "sinv",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_40

def body641_42 : Prog (BitVec 64) :=
.decCall ("sinv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("modinv_bin") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_41

def body641_43 : Prog (BitVec 64) :=
.seq body641_11 body641_42

def body641_44 : Prog (BitVec 64) :=
.decCall ("elt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "e",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_43

def body641_45 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hash32", Flapjack.Exp.const 32#64]) body641_44

def body641_46 : Prog (BitVec 64) :=
.seq body641_9 body641_45

def body641_47 : Prog (BitVec 64) :=
.decCall ("onc") (Flapjack.Shape.one) ("p256_on_curve") ([Flapjack.Exp.var Flapjack.VarKind.local "qx", Flapjack.Exp.var Flapjack.VarKind.local "qy"]) body641_46

def body641_48 : Prog (BitVec 64) :=
.seq body641_8 body641_47

def body641_49 : Prog (BitVec 64) :=
.seq body641_7 body641_48

def body641_50 : Prog (BitVec 64) :=
.decCall ("ylt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "qy",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) body641_49

def body641_51 : Prog (BitVec 64) :=
.seq body641_6 body641_50

def body641_52 : Prog (BitVec 64) :=
.decCall ("xlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "qx",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) body641_51

def body641_53 : Prog (BitVec 64) :=
.seq body641_5 body641_52

def body641_54 : Prog (BitVec 64) :=
.decCall ("slt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_53

def body641_55 : Prog (BitVec 64) :=
.seq body641_4 body641_54

def body641_56 : Prog (BitVec 64) :=
.decCall ("sz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "s"]) body641_55

def body641_57 : Prog (BitVec 64) :=
.seq body641_3 body641_56

def body641_58 : Prog (BitVec 64) :=
.decCall ("rlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_57

def body641_59 : Prog (BitVec 64) :=
.seq body641_2 body641_58

def body641_60 : Prog (BitVec 64) :=
.decCall ("rz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) body641_59

def body641_61 : Prog (BitVec 64) :=
.seq body641_7 body641_8

def body641_62 : Prog (BitVec 64) :=
.seq body641_19 body641_20

def body641_63 : Prog (BitVec 64) :=
.seq body641_62 body641_21

def body641_64 : Prog (BitVec 64) :=
.decCall ("rnlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "rn4",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) body641_63

def body641_65 : Prog (BitVec 64) :=
.dec ("rn4") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "rn")]) body641_64

def body641_66 : Prog (BitVec 64) :=
.seq body641_18 body641_65

def body641_67 : Prog (BitVec 64) :=
.decCall ("rn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_66

def body641_68 : Prog (BitVec 64) :=
.seq body641_17 body641_67

def body641_69 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "x"]) body641_68

def body641_70 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) body641_69

def body641_71 : Prog (BitVec 64) :=
.seq body641_13 body641_70

def body641_72 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pr")) body641_71

def body641_73 : Prog (BitVec 64) :=
.decCall ("z2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) body641_72

def body641_74 : Prog (BitVec 64) :=
.seq body641_15 body641_73

def body641_75 : Prog (BitVec 64) :=
.decCall ("zz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) body641_74

def body641_76 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pr", Flapjack.Exp.const 64#64])) body641_75

def body641_77 : Prog (BitVec 64) :=
.seq body641_12 body641_76

def body641_78 : Prog (BitVec 64) :=
.decCall ("pr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body641_77

def body641_79 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body641_78

def body641_80 : Prog (BitVec 64) :=
.decCall ("u2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mulmod") ([Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "sinv",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_79

def body641_81 : Prog (BitVec 64) :=
.decCall ("u1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mulmod") ([Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.var Flapjack.VarKind.local "sinv",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_80

def body641_82 : Prog (BitVec 64) :=
.decCall ("sinv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("modinv_bin") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_81

def body641_83 : Prog (BitVec 64) :=
.seq body641_11 body641_82

def body641_84 : Prog (BitVec 64) :=
.decCall ("elt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "e",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_83

def body641_85 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hash32", Flapjack.Exp.const 32#64]) body641_84

def body641_86 : Prog (BitVec 64) :=
.seq body641_9 body641_85

def body641_87 : Prog (BitVec 64) :=
.decCall ("onc") (Flapjack.Shape.one) ("p256_on_curve") ([Flapjack.Exp.var Flapjack.VarKind.local "qx", Flapjack.Exp.var Flapjack.VarKind.local "qy"]) body641_86

def body641_88 : Prog (BitVec 64) :=
.seq body641_61 body641_87

def body641_89 : Prog (BitVec 64) :=
.decCall ("ylt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "qy",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) body641_88

def body641_90 : Prog (BitVec 64) :=
.seq body641_6 body641_89

def body641_91 : Prog (BitVec 64) :=
.decCall ("xlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "qx",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) body641_90

def body641_92 : Prog (BitVec 64) :=
.seq body641_5 body641_91

def body641_93 : Prog (BitVec 64) :=
.decCall ("slt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_92

def body641_94 : Prog (BitVec 64) :=
.seq body641_4 body641_93

def body641_95 : Prog (BitVec 64) :=
.decCall ("sz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "s"]) body641_94

def body641_96 : Prog (BitVec 64) :=
.seq body641_3 body641_95

def body641_97 : Prog (BitVec 64) :=
.decCall ("rlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) body641_96

def body641_98 : Prog (BitVec 64) :=
.seq body641_2 body641_97

def body641_99 : Prog (BitVec 64) :=
.decCall ("rz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) body641_98

def originalData641 : Decl (BitVec 64) :=
.function { name := "p256_verify", inline := false, exported := false, params := [("hash32", Flapjack.Shape.one),
  ("r", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("s", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("qx", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("qy", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body641_60, returnShape := (Flapjack.Shape.one) }
def simplifiedData641 : Decl (BitVec 64) :=
.function { name := "p256_verify", inline := false, exported := false, params := [("hash32", Flapjack.Shape.one),
  ("r", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("s", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("qx", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("qy", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := body641_99, returnShape := (Flapjack.Shape.one) }
def original641 := Pancake.PanLang.declToHOL originalData641
def simplified641 := Pancake.PanLang.declToHOL simplifiedData641
end InitECandidate.Proofs.FrontendStages.Declarations
