import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data641
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate625
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody641_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody641_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody641_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rz") (Flapjack.Exp.const 1#64)) globalBody641_0 globalBody641_1

def globalBody641_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rlt") (Flapjack.Exp.const 0#64)) globalBody641_0 globalBody641_1

def globalBody641_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sz") (Flapjack.Exp.const 1#64)) globalBody641_0 globalBody641_1

def globalBody641_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "slt") (Flapjack.Exp.const 0#64)) globalBody641_0 globalBody641_1

def globalBody641_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "xlt") (Flapjack.Exp.const 0#64)) globalBody641_0 globalBody641_1

def globalBody641_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ylt") (Flapjack.Exp.const 0#64)) globalBody641_0 globalBody641_1

def globalBody641_8 : Prog (BitVec 64) :=
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
  (Flapjack.Exp.const 0#64)) globalBody641_0 globalBody641_1

def globalBody641_9 : Prog (BitVec 64) :=
.seq globalBody641_7 globalBody641_8

def globalBody641_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "onc") (Flapjack.Exp.const 0#64)) globalBody641_0 globalBody641_1

def globalBody641_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "e"), none)) "u256_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "e",
    Flapjack.Exp.rStruct
      [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
        Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]

def globalBody641_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "elt") (Flapjack.Exp.const 0#64)) globalBody641_11 globalBody641_1

def globalBody641_13 : Prog (BitVec 64) :=
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

def globalBody641_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody641_15 : Prog (BitVec 64) :=
.seq globalBody641_14 globalBody641_0

def globalBody641_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "zz") (Flapjack.Exp.const 1#64)) globalBody641_15 globalBody641_1

def globalBody641_17 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody641_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 1#64)) globalBody641_17 globalBody641_1

def globalBody641_19 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "rn"))
  (Flapjack.Exp.const 1#64)) globalBody641_0 globalBody641_1

def globalBody641_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "rnlt") (Flapjack.Exp.const 0#64)) globalBody641_0 globalBody641_1

def globalBody641_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "p256_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "rn4", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def globalBody641_22 : Prog (BitVec 64) :=
.seq globalBody641_20 globalBody641_21

def globalBody641_23 : Prog (BitVec 64) :=
Flapjack.Prog.call none "u256_eq"
  [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "x"]

def globalBody641_24 : Prog (BitVec 64) :=
.seq globalBody641_22 globalBody641_23

def globalBody641_25 : Prog (BitVec 64) :=
.decCall ("rnlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "rn4",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) globalBody641_24

def globalBody641_26 : Prog (BitVec 64) :=
.dec ("rn4") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "rn"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "rn")]) globalBody641_25

def globalBody641_27 : Prog (BitVec 64) :=
.seq globalBody641_19 globalBody641_26

def globalBody641_28 : Prog (BitVec 64) :=
.decCall ("rn") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_add_carry") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) globalBody641_27

def globalBody641_29 : Prog (BitVec 64) :=
.seq globalBody641_18 globalBody641_28

def globalBody641_30 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.var Flapjack.VarKind.local "x"]) globalBody641_29

def globalBody641_31 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) globalBody641_30

def globalBody641_32 : Prog (BitVec 64) :=
.seq globalBody641_14 globalBody641_31

def globalBody641_33 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pr")) globalBody641_32

def globalBody641_34 : Prog (BitVec 64) :=
.decCall ("z2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) globalBody641_33

def globalBody641_35 : Prog (BitVec 64) :=
.seq globalBody641_16 globalBody641_34

def globalBody641_36 : Prog (BitVec 64) :=
.decCall ("zz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) globalBody641_35

def globalBody641_37 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pr", Flapjack.Exp.const 64#64])) globalBody641_36

def globalBody641_38 : Prog (BitVec 64) :=
.seq globalBody641_13 globalBody641_37

def globalBody641_39 : Prog (BitVec 64) :=
.decCall ("pr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) globalBody641_38

def globalBody641_40 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody641_39

def globalBody641_41 : Prog (BitVec 64) :=
.decCall ("u2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mulmod") ([Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "sinv",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) globalBody641_40

def globalBody641_42 : Prog (BitVec 64) :=
.decCall ("u1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_mulmod") ([Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.var Flapjack.VarKind.local "sinv",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) globalBody641_41

def globalBody641_43 : Prog (BitVec 64) :=
.decCall ("sinv") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("modinv_bin") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) globalBody641_42

def globalBody641_44 : Prog (BitVec 64) :=
.seq globalBody641_12 globalBody641_43

def globalBody641_45 : Prog (BitVec 64) :=
.decCall ("elt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "e",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) globalBody641_44

def globalBody641_46 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "hash32", Flapjack.Exp.const 32#64]) globalBody641_45

def globalBody641_47 : Prog (BitVec 64) :=
.seq globalBody641_10 globalBody641_46

def globalBody641_48 : Prog (BitVec 64) :=
.decCall ("onc") (Flapjack.Shape.one) ("p256_on_curve") ([Flapjack.Exp.var Flapjack.VarKind.local "qx", Flapjack.Exp.var Flapjack.VarKind.local "qy"]) globalBody641_47

def globalBody641_49 : Prog (BitVec 64) :=
.seq globalBody641_9 globalBody641_48

def globalBody641_50 : Prog (BitVec 64) :=
.decCall ("ylt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "qy",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) globalBody641_49

def globalBody641_51 : Prog (BitVec 64) :=
.seq globalBody641_6 globalBody641_50

def globalBody641_52 : Prog (BitVec 64) :=
.decCall ("xlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "qx",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 4294967295#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 18446744069414584321#64]]) globalBody641_51

def globalBody641_53 : Prog (BitVec 64) :=
.seq globalBody641_5 globalBody641_52

def globalBody641_54 : Prog (BitVec 64) :=
.decCall ("slt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "s",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) globalBody641_53

def globalBody641_55 : Prog (BitVec 64) :=
.seq globalBody641_4 globalBody641_54

def globalBody641_56 : Prog (BitVec 64) :=
.decCall ("sz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "s"]) globalBody641_55

def globalBody641_57 : Prog (BitVec 64) :=
.seq globalBody641_3 globalBody641_56

def globalBody641_58 : Prog (BitVec 64) :=
.decCall ("rlt") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "r",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 17562291160714782033#64, Flapjack.Exp.const 13611842547513532036#64,
      Flapjack.Exp.const 18446744073709551615#64, Flapjack.Exp.const 18446744069414584320#64]]) globalBody641_57

def globalBody641_59 : Prog (BitVec 64) :=
.seq globalBody641_2 globalBody641_58

def globalBody641_60 : Prog (BitVec 64) :=
.decCall ("rz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "r"]) globalBody641_59

def globalData641 : Decl (BitVec 64) :=
.function { name := "p256_verify", inline := false, exported := false, params := [("hash32", Flapjack.Shape.one),
  ("r", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("s", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("qx", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("qy", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody641_60, returnShape := (Flapjack.Shape.one) }
def globalOutput641 := Pancake.PanLang.declToHOL globalData641
end InitECandidate.Proofs.FrontendStages.Declarations
