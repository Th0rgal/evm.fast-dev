import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify668
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body684_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body684_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body684_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.var Flapjack.VarKind.local "l0", Flapjack.Exp.var Flapjack.VarKind.local "l1",
      Flapjack.Exp.var Flapjack.VarKind.local "l2", Flapjack.Exp.var Flapjack.VarKind.local "l3"])
  (Flapjack.Exp.const 0#64)) body684_0 body684_1

def body684_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_set_inf"
  [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body684_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body684_5 : Prog (BitVec 64) :=
.seq body684_3 body684_4

def body684_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "z") (Flapjack.Exp.const 1#64)) body684_5 body684_1

def body684_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x0"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "x0"]

def body684_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x1"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def body684_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y0"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "y0"]

def body684_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y1"), none)) "fq_to_mont"
  [Flapjack.Exp.var Flapjack.VarKind.local "y1"]

def body684_11 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "out") (Flapjack.Exp.var Flapjack.VarKind.local "x0")

def body684_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "x1")

def body684_13 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y0")

def body684_14 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y1")

def body684_15 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 128#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 15230403791020821917#64, Flapjack.Exp.const 754611498739239741#64,
      Flapjack.Exp.const 7381016538464732716#64, Flapjack.Exp.const 1011752739694698287#64])

def body684_16 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 160#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body684_17 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "b2")
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4321547867055981224#64, Flapjack.Exp.const 147241268046680925#64,
      Flapjack.Exp.const 2789960110459671136#64, Flapjack.Exp.const 2671978398120978541#64])

def body684_18 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b2", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4100506350182530919#64, Flapjack.Exp.const 7345568344173317438#64,
      Flapjack.Exp.const 15513160039642431658#64, Flapjack.Exp.const 90557763186888013#64])

def body684_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64]]

def body684_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "out",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body684_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body684_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_add"
  [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "b2"]

def body684_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body684_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) body684_0 body684_1

def body684_25 : Prog (BitVec 64) :=
.seq body684_24 body684_4

def body684_26 : Prog (BitVec 64) :=
.seq body684_23 body684_25

def body684_27 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.const 64#64]) body684_26

def body684_28 : Prog (BitVec 64) :=
.seq body684_22 body684_27

def body684_29 : Prog (BitVec 64) :=
.seq body684_21 body684_28

def body684_30 : Prog (BitVec 64) :=
.seq body684_20 body684_29

def body684_31 : Prog (BitVec 64) :=
.seq body684_19 body684_30

def body684_32 : Prog (BitVec 64) :=
.seq body684_18 body684_31

def body684_33 : Prog (BitVec 64) :=
.seq body684_17 body684_32

def body684_34 : Prog (BitVec 64) :=
.decCall ("b2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body684_33

def body684_35 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body684_34

def body684_36 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body684_35

def body684_37 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body684_36

def body684_38 : Prog (BitVec 64) :=
.seq body684_16 body684_37

def body684_39 : Prog (BitVec 64) :=
.seq body684_15 body684_38

def body684_40 : Prog (BitVec 64) :=
.seq body684_14 body684_39

def body684_41 : Prog (BitVec 64) :=
.seq body684_13 body684_40

def body684_42 : Prog (BitVec 64) :=
.seq body684_12 body684_41

def body684_43 : Prog (BitVec 64) :=
.seq body684_11 body684_42

def body684_44 : Prog (BitVec 64) :=
.seq body684_10 body684_43

def body684_45 : Prog (BitVec 64) :=
.seq body684_9 body684_44

def body684_46 : Prog (BitVec 64) :=
.seq body684_8 body684_45

def body684_47 : Prog (BitVec 64) :=
.seq body684_7 body684_46

def body684_48 : Prog (BitVec 64) :=
.seq body684_6 body684_47

def body684_49 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64]) body684_48

def body684_50 : Prog (BitVec 64) :=
.seq body684_2 body684_49

def body684_51 : Prog (BitVec 64) :=
.decCall ("l3") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y1",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_50

def body684_52 : Prog (BitVec 64) :=
.decCall ("l2") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y0",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_51

def body684_53 : Prog (BitVec 64) :=
.decCall ("l1") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x1",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_52

def body684_54 : Prog (BitVec 64) :=
.decCall ("l0") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x0",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_53

def body684_55 : Prog (BitVec 64) :=
.decCall ("y0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
  Flapjack.Exp.const 32#64]) body684_54

def body684_56 : Prog (BitVec 64) :=
.decCall ("y1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body684_55

def body684_57 : Prog (BitVec 64) :=
.decCall ("x0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body684_56

def body684_58 : Prog (BitVec 64) :=
.decCall ("x1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) body684_57

def body684_59 : Prog (BitVec 64) :=
.seq body684_6 body684_7

def body684_60 : Prog (BitVec 64) :=
.seq body684_59 body684_8

def body684_61 : Prog (BitVec 64) :=
.seq body684_60 body684_9

def body684_62 : Prog (BitVec 64) :=
.seq body684_61 body684_10

def body684_63 : Prog (BitVec 64) :=
.seq body684_62 body684_11

def body684_64 : Prog (BitVec 64) :=
.seq body684_63 body684_12

def body684_65 : Prog (BitVec 64) :=
.seq body684_64 body684_13

def body684_66 : Prog (BitVec 64) :=
.seq body684_65 body684_14

def body684_67 : Prog (BitVec 64) :=
.seq body684_66 body684_15

def body684_68 : Prog (BitVec 64) :=
.seq body684_67 body684_16

def body684_69 : Prog (BitVec 64) :=
.seq body684_17 body684_18

def body684_70 : Prog (BitVec 64) :=
.seq body684_69 body684_19

def body684_71 : Prog (BitVec 64) :=
.seq body684_70 body684_20

def body684_72 : Prog (BitVec 64) :=
.seq body684_71 body684_21

def body684_73 : Prog (BitVec 64) :=
.seq body684_72 body684_22

def body684_74 : Prog (BitVec 64) :=
.seq body684_23 body684_24

def body684_75 : Prog (BitVec 64) :=
.seq body684_74 body684_4

def body684_76 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.const 64#64]) body684_75

def body684_77 : Prog (BitVec 64) :=
.seq body684_73 body684_76

def body684_78 : Prog (BitVec 64) :=
.decCall ("b2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body684_77

def body684_79 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body684_78

def body684_80 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 64#64]) body684_79

def body684_81 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body684_80

def body684_82 : Prog (BitVec 64) :=
.seq body684_68 body684_81

def body684_83 : Prog (BitVec 64) :=
.decCall ("z") (Flapjack.Shape.one) ("is_zero_bytes") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64]) body684_82

def body684_84 : Prog (BitVec 64) :=
.seq body684_2 body684_83

def body684_85 : Prog (BitVec 64) :=
.decCall ("l3") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y1",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_84

def body684_86 : Prog (BitVec 64) :=
.decCall ("l2") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "y0",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_85

def body684_87 : Prog (BitVec 64) :=
.decCall ("l1") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x1",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_86

def body684_88 : Prog (BitVec 64) :=
.decCall ("l0") (Flapjack.Shape.one) ("u256_lt") ([Flapjack.Exp.var Flapjack.VarKind.local "x0",
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 4332616871279656263#64, Flapjack.Exp.const 10917124144477883021#64,
      Flapjack.Exp.const 13281191951274694749#64, Flapjack.Exp.const 3486998266802970665#64]]) body684_87

def body684_89 : Prog (BitVec 64) :=
.decCall ("y0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 96#64],
  Flapjack.Exp.const 32#64]) body684_88

def body684_90 : Prog (BitVec 64) :=
.decCall ("y1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 64#64],
  Flapjack.Exp.const 32#64]) body684_89

def body684_91 : Prog (BitVec 64) :=
.decCall ("x0") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64],
  Flapjack.Exp.const 32#64]) body684_90

def body684_92 : Prog (BitVec 64) :=
.decCall ("x1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 32#64]) body684_91

def originalData684 : Decl (BitVec 64) :=
.function { name := "bn254_parse_g2", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body684_58, returnShape := (Flapjack.Shape.one) }
def simplifiedData684 : Decl (BitVec 64) :=
.function { name := "bn254_parse_g2", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body684_92, returnShape := (Flapjack.Shape.one) }
def original684 := Pancake.PanLang.declToHOL originalData684
def simplified684 := Pancake.PanLang.declToHOL simplifiedData684
end InitECandidate.Proofs.FrontendStages.Declarations
