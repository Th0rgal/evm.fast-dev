import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify781
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body797_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "g2",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 480#64]]

def body797_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g2", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 576#64]]

def body797_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g2", Flapjack.Exp.const 192#64]]

def body797_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "kzg_neg_scalar"
  [Flapjack.Exp.var Flapjack.VarKind.local "zb", Flapjack.Exp.var Flapjack.VarKind.local "k"]

def body797_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "xmz", Flapjack.Exp.var Flapjack.VarKind.local "g2",
    Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 4#64]

def body797_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "setup",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 672#64]]

def body797_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "setup", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 768#64]]

def body797_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_set_one"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "setup", Flapjack.Exp.const 192#64]]

def body797_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "xmz", Flapjack.Exp.var Flapjack.VarKind.local "setup",
    Flapjack.Exp.var Flapjack.VarKind.local "xmz"]

def body797_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "g1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 384#64],
    Flapjack.Exp.const 48#64]

def body797_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g1", Flapjack.Exp.const 48#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 432#64],
    Flapjack.Exp.const 48#64]

def body797_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "g1", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
      Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
      Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64])

def body797_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "kzg_neg_scalar"
  [Flapjack.Exp.var Flapjack.VarKind.local "yb", Flapjack.Exp.var Flapjack.VarKind.local "k"]

def body797_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "pmy", Flapjack.Exp.var Flapjack.VarKind.local "g1",
    Flapjack.Exp.var Flapjack.VarKind.local "k", Flapjack.Exp.const 4#64]

def body797_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "pmy", Flapjack.Exp.var Flapjack.VarKind.local "commitment",
    Flapjack.Exp.var Flapjack.VarKind.local "pmy"]

def body797_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "g2", Flapjack.Exp.var Flapjack.VarKind.local "g2"]

def body797_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body797_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_accumulate"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "pmy",
    Flapjack.Exp.var Flapjack.VarKind.local "g2"]

def body797_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_accumulate"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "proof",
    Flapjack.Exp.var Flapjack.VarKind.local "xmz"]

def body797_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_final_exp"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body797_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body797_21 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "one")

def body797_22 : Prog (BitVec 64) :=
.seq body797_20 body797_21

def body797_23 : Prog (BitVec 64) :=
.decCall ("one") (Flapjack.Shape.one) ("fp12_is_one") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) body797_22

def body797_24 : Prog (BitVec 64) :=
.seq body797_19 body797_23

def body797_25 : Prog (BitVec 64) :=
.seq body797_18 body797_24

def body797_26 : Prog (BitVec 64) :=
.seq body797_17 body797_25

def body797_27 : Prog (BitVec 64) :=
.seq body797_16 body797_26

def body797_28 : Prog (BitVec 64) :=
.seq body797_15 body797_27

def body797_29 : Prog (BitVec 64) :=
.seq body797_14 body797_28

def body797_30 : Prog (BitVec 64) :=
.seq body797_13 body797_29

def body797_31 : Prog (BitVec 64) :=
.seq body797_12 body797_30

def body797_32 : Prog (BitVec 64) :=
.seq body797_11 body797_31

def body797_33 : Prog (BitVec 64) :=
.seq body797_10 body797_32

def body797_34 : Prog (BitVec 64) :=
.seq body797_9 body797_33

def body797_35 : Prog (BitVec 64) :=
.seq body797_8 body797_34

def body797_36 : Prog (BitVec 64) :=
.seq body797_7 body797_35

def body797_37 : Prog (BitVec 64) :=
.seq body797_6 body797_36

def body797_38 : Prog (BitVec 64) :=
.seq body797_5 body797_37

def body797_39 : Prog (BitVec 64) :=
.seq body797_4 body797_38

def body797_40 : Prog (BitVec 64) :=
.seq body797_3 body797_39

def body797_41 : Prog (BitVec 64) :=
.seq body797_2 body797_40

def body797_42 : Prog (BitVec 64) :=
.seq body797_1 body797_41

def body797_43 : Prog (BitVec 64) :=
.seq body797_0 body797_42

def body797_44 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body797_43

def body797_45 : Prog (BitVec 64) :=
.decCall ("xmz") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body797_44

def body797_46 : Prog (BitVec 64) :=
.decCall ("pmy") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body797_45

def body797_47 : Prog (BitVec 64) :=
.decCall ("setup") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body797_46

def body797_48 : Prog (BitVec 64) :=
.decCall ("g2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body797_47

def body797_49 : Prog (BitVec 64) :=
.decCall ("g1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body797_48

def body797_50 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body797_49

def body797_51 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body797_50

def body797_52 : Prog (BitVec 64) :=
.seq body797_0 body797_1

def body797_53 : Prog (BitVec 64) :=
.seq body797_52 body797_2

def body797_54 : Prog (BitVec 64) :=
.seq body797_53 body797_3

def body797_55 : Prog (BitVec 64) :=
.seq body797_54 body797_4

def body797_56 : Prog (BitVec 64) :=
.seq body797_55 body797_5

def body797_57 : Prog (BitVec 64) :=
.seq body797_56 body797_6

def body797_58 : Prog (BitVec 64) :=
.seq body797_57 body797_7

def body797_59 : Prog (BitVec 64) :=
.seq body797_58 body797_8

def body797_60 : Prog (BitVec 64) :=
.seq body797_59 body797_9

def body797_61 : Prog (BitVec 64) :=
.seq body797_60 body797_10

def body797_62 : Prog (BitVec 64) :=
.seq body797_61 body797_11

def body797_63 : Prog (BitVec 64) :=
.seq body797_62 body797_12

def body797_64 : Prog (BitVec 64) :=
.seq body797_63 body797_13

def body797_65 : Prog (BitVec 64) :=
.seq body797_64 body797_14

def body797_66 : Prog (BitVec 64) :=
.seq body797_65 body797_15

def body797_67 : Prog (BitVec 64) :=
.seq body797_66 body797_16

def body797_68 : Prog (BitVec 64) :=
.seq body797_67 body797_17

def body797_69 : Prog (BitVec 64) :=
.seq body797_68 body797_18

def body797_70 : Prog (BitVec 64) :=
.seq body797_69 body797_19

def body797_71 : Prog (BitVec 64) :=
.seq body797_70 body797_23

def body797_72 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body797_71

def body797_73 : Prog (BitVec 64) :=
.decCall ("xmz") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body797_72

def body797_74 : Prog (BitVec 64) :=
.decCall ("pmy") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body797_73

def body797_75 : Prog (BitVec 64) :=
.decCall ("setup") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body797_74

def body797_76 : Prog (BitVec 64) :=
.decCall ("g2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body797_75

def body797_77 : Prog (BitVec 64) :=
.decCall ("g1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body797_76

def body797_78 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body797_77

def body797_79 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body797_78

def originalData797 : Decl (BitVec 64) :=
.function { name := "kzg_verify", inline := false, exported := false, params := [("commitment", Flapjack.Shape.one), ("zb", Flapjack.Shape.one), ("yb", Flapjack.Shape.one),
  ("proof", Flapjack.Shape.one)], body := body797_51, returnShape := (Flapjack.Shape.one) }
def simplifiedData797 : Decl (BitVec 64) :=
.function { name := "kzg_verify", inline := false, exported := false, params := [("commitment", Flapjack.Shape.one), ("zb", Flapjack.Shape.one), ("yb", Flapjack.Shape.one),
  ("proof", Flapjack.Shape.one)], body := body797_79, returnShape := (Flapjack.Shape.one) }
def original797 := Pancake.PanLang.declToHOL originalData797
def simplified797 := Pancake.PanLang.declToHOL simplifiedData797
end InitECandidate.Proofs.FrontendStages.Declarations
