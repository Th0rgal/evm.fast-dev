import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify778
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body794_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body794_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body794_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "c_flag") (Flapjack.Exp.const 1#64)) body794_0 body794_1

def body794_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "xb", Flapjack.Exp.var Flapjack.VarKind.local "bs", Flapjack.Exp.const 48#64]

def body794_4 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte (Flapjack.Exp.var Flapjack.VarKind.local "xb")
  (Flapjack.Exp.op Flapjack.BinOp.and [Flapjack.Exp.var Flapjack.VarKind.local "top", Flapjack.Exp.const 31#64])

def body794_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body794_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.const 0#64)
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "xz") (Flapjack.Exp.const 0#64),
      Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "a_flag") (Flapjack.Exp.const 1#64)])) body794_0 body794_1

def body794_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def body794_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body794_9 : Prog (BitVec 64) :=
.seq body794_7 body794_8

def body794_10 : Prog (BitVec 64) :=
.seq body794_6 body794_9

def body794_11 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "xc"]) body794_10

def body794_12 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "b_flag") (Flapjack.Exp.const 1#64)) body794_11 body794_1

def body794_13 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "lt") (Flapjack.Exp.const 0#64)) body794_0 body794_1

def body794_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "rhs"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "rhs", Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body794_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "rhs"), none)) "bls_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "rhs", Flapjack.Exp.var Flapjack.VarKind.local "b"]

def body794_16 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sq") (Flapjack.Exp.const 0#64)) body794_0 body794_1

def body794_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body794_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "hi")
  (Flapjack.Exp.var Flapjack.VarKind.local "a_flag")) body794_17 body794_1

def body794_19 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "x")

def body794_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y")

def body794_21 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
      Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
      Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64])

def body794_22 : Prog (BitVec 64) :=
.seq body794_21 body794_8

def body794_23 : Prog (BitVec 64) :=
.seq body794_20 body794_22

def body794_24 : Prog (BitVec 64) :=
.seq body794_19 body794_23

def body794_25 : Prog (BitVec 64) :=
.seq body794_18 body794_24

def body794_26 : Prog (BitVec 64) :=
.decCall ("hi") (Flapjack.Shape.one) ("bls_fp_is_high") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body794_25

def body794_27 : Prog (BitVec 64) :=
.seq body794_16 body794_26

def body794_28 : Prog (BitVec 64) :=
.decCall ("sq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "rhs"]) body794_27

def body794_29 : Prog (BitVec 64) :=
.decCall ("chk") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body794_28

def body794_30 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_pow") ([Flapjack.Exp.var Flapjack.VarKind.local "rhs",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1432#64],
  Flapjack.Exp.const 6#64]) body794_29

def body794_31 : Prog (BitVec 64) :=
.seq body794_15 body794_30

def body794_32 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 240#64])) body794_31

def body794_33 : Prog (BitVec 64) :=
.seq body794_14 body794_32

def body794_34 : Prog (BitVec 64) :=
.decCall ("rhs") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "x"]) body794_33

def body794_35 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_to_mont") ([Flapjack.Exp.var Flapjack.VarKind.local "xc"]) body794_34

def body794_36 : Prog (BitVec 64) :=
.seq body794_13 body794_35

def body794_37 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("bls_fp_lt_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "xc",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13402431016077863595#64, Flapjack.Exp.const 2210141511517208575#64,
      Flapjack.Exp.const 7435674573564081700#64, Flapjack.Exp.const 7239337960414712511#64,
      Flapjack.Exp.const 5412103778470702295#64, Flapjack.Exp.const 1873798617647539866#64]]) body794_36

def body794_38 : Prog (BitVec 64) :=
.seq body794_12 body794_37

def body794_39 : Prog (BitVec 64) :=
.seq body794_5 body794_38

def body794_40 : Prog (BitVec 64) :=
.decCall ("xc") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_from_be48") ([Flapjack.Exp.var Flapjack.VarKind.local "xb"]) body794_39

def body794_41 : Prog (BitVec 64) :=
.seq body794_4 body794_40

def body794_42 : Prog (BitVec 64) :=
.seq body794_3 body794_41

def body794_43 : Prog (BitVec 64) :=
.decCall ("xb") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 48#64]) body794_42

def body794_44 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body794_43

def body794_45 : Prog (BitVec 64) :=
.seq body794_2 body794_44

def body794_46 : Prog (BitVec 64) :=
.dec ("a_flag") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 5#64),
    Flapjack.Exp.const 1#64]) body794_45

def body794_47 : Prog (BitVec 64) :=
.dec ("b_flag") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 6#64),
    Flapjack.Exp.const 1#64]) body794_46

def body794_48 : Prog (BitVec 64) :=
.dec ("c_flag") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 7#64),
    Flapjack.Exp.const 1#64]) body794_47

def body794_49 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "bs")) body794_48

def body794_50 : Prog (BitVec 64) :=
.seq body794_3 body794_4

def body794_51 : Prog (BitVec 64) :=
.seq body794_6 body794_7

def body794_52 : Prog (BitVec 64) :=
.seq body794_51 body794_8

def body794_53 : Prog (BitVec 64) :=
.decCall ("xz") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "xc"]) body794_52

def body794_54 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "b_flag") (Flapjack.Exp.const 1#64)) body794_53 body794_1

def body794_55 : Prog (BitVec 64) :=
.seq body794_5 body794_54

def body794_56 : Prog (BitVec 64) :=
.seq body794_18 body794_19

def body794_57 : Prog (BitVec 64) :=
.seq body794_56 body794_20

def body794_58 : Prog (BitVec 64) :=
.seq body794_57 body794_21

def body794_59 : Prog (BitVec 64) :=
.seq body794_58 body794_8

def body794_60 : Prog (BitVec 64) :=
.decCall ("hi") (Flapjack.Shape.one) ("bls_fp_is_high") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body794_59

def body794_61 : Prog (BitVec 64) :=
.seq body794_16 body794_60

def body794_62 : Prog (BitVec 64) :=
.decCall ("sq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "chk", Flapjack.Exp.var Flapjack.VarKind.local "rhs"]) body794_61

def body794_63 : Prog (BitVec 64) :=
.decCall ("chk") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) body794_62

def body794_64 : Prog (BitVec 64) :=
.decCall ("y") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_pow") ([Flapjack.Exp.var Flapjack.VarKind.local "rhs",
  Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1432#64],
  Flapjack.Exp.const 6#64]) body794_63

def body794_65 : Prog (BitVec 64) :=
.seq body794_15 body794_64

def body794_66 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 240#64])) body794_65

def body794_67 : Prog (BitVec 64) :=
.seq body794_14 body794_66

def body794_68 : Prog (BitVec 64) :=
.decCall ("rhs") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "x"]) body794_67

def body794_69 : Prog (BitVec 64) :=
.decCall ("x") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_to_mont") ([Flapjack.Exp.var Flapjack.VarKind.local "xc"]) body794_68

def body794_70 : Prog (BitVec 64) :=
.seq body794_13 body794_69

def body794_71 : Prog (BitVec 64) :=
.decCall ("lt") (Flapjack.Shape.one) ("bls_fp_lt_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "xc",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 13402431016077863595#64, Flapjack.Exp.const 2210141511517208575#64,
      Flapjack.Exp.const 7435674573564081700#64, Flapjack.Exp.const 7239337960414712511#64,
      Flapjack.Exp.const 5412103778470702295#64, Flapjack.Exp.const 1873798617647539866#64]]) body794_70

def body794_72 : Prog (BitVec 64) :=
.seq body794_55 body794_71

def body794_73 : Prog (BitVec 64) :=
.decCall ("xc") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_from_be48") ([Flapjack.Exp.var Flapjack.VarKind.local "xb"]) body794_72

def body794_74 : Prog (BitVec 64) :=
.seq body794_50 body794_73

def body794_75 : Prog (BitVec 64) :=
.decCall ("xb") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 48#64]) body794_74

def body794_76 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body794_75

def body794_77 : Prog (BitVec 64) :=
.seq body794_2 body794_76

def body794_78 : Prog (BitVec 64) :=
.dec ("a_flag") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 5#64),
    Flapjack.Exp.const 1#64]) body794_77

def body794_79 : Prog (BitVec 64) :=
.dec ("b_flag") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 6#64),
    Flapjack.Exp.const 1#64]) body794_78

def body794_80 : Prog (BitVec 64) :=
.dec ("c_flag") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.and
  [Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "top") (Flapjack.Exp.const 7#64),
    Flapjack.Exp.const 1#64]) body794_79

def body794_81 : Prog (BitVec 64) :=
.dec ("top") (Flapjack.Shape.one) (Flapjack.Exp.loadByte (Flapjack.Exp.var Flapjack.VarKind.local "bs")) body794_80

def originalData794 : Decl (BitVec 64) :=
.function { name := "kzg_decompress_g1", inline := false, exported := false, params := [("bs", Flapjack.Shape.one), ("r", Flapjack.Shape.one)], body := body794_49, returnShape := (Flapjack.Shape.one) }
def simplifiedData794 : Decl (BitVec 64) :=
.function { name := "kzg_decompress_g1", inline := false, exported := false, params := [("bs", Flapjack.Shape.one), ("r", Flapjack.Shape.one)], body := body794_81, returnShape := (Flapjack.Shape.one) }
def original794 := Pancake.PanLang.declToHOL originalData794
def simplified794 := Pancake.PanLang.declToHOL simplifiedData794
end InitECandidate.Proofs.FrontendStages.Declarations
