import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify787
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body803_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body803_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body803_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body803_3 : Prog (BitVec 64) :=
.seq body803_1 body803_2

def body803_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body803_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body803_3 body803_4

def body803_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sg") (Flapjack.Exp.const 0#64)) body803_3 body803_4

def body803_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "g2_decode"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 128#64],
    Flapjack.Exp.var Flapjack.VarKind.local "q"]

def body803_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "sg"), none)) "g2_subgroup_check"
  [Flapjack.Exp.var Flapjack.VarKind.local "q"]

def body803_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "pair_accumulate"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "q"]

def body803_10 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body803_11 : Prog (BitVec 64) :=
.seq body803_9 body803_10

def body803_12 : Prog (BitVec 64) :=
.seq body803_6 body803_11

def body803_13 : Prog (BitVec 64) :=
.seq body803_8 body803_12

def body803_14 : Prog (BitVec 64) :=
.seq body803_5 body803_13

def body803_15 : Prog (BitVec 64) :=
.seq body803_7 body803_14

def body803_16 : Prog (BitVec 64) :=
.seq body803_6 body803_15

def body803_17 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g1_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body803_16

def body803_18 : Prog (BitVec 64) :=
.seq body803_5 body803_17

def body803_19 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g1_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) body803_18

def body803_20 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 384#64]]) body803_19

def body803_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) body803_20

def body803_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_final_exp"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc"]

def body803_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 32#64]

def body803_24 : Prog (BitVec 64) :=
Flapjack.Prog.storeByte
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 31#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "one")

def body803_25 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body803_26 : Prog (BitVec 64) :=
.seq body803_1 body803_25

def body803_27 : Prog (BitVec 64) :=
.seq body803_24 body803_26

def body803_28 : Prog (BitVec 64) :=
.seq body803_23 body803_27

def body803_29 : Prog (BitVec 64) :=
.decCall ("one") (Flapjack.Shape.one) ("fp12_is_one") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) body803_28

def body803_30 : Prog (BitVec 64) :=
.seq body803_22 body803_29

def body803_31 : Prog (BitVec 64) :=
.seq body803_21 body803_30

def body803_32 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body803_31

def body803_33 : Prog (BitVec 64) :=
.seq body803_0 body803_32

def body803_34 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body803_33

def body803_35 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body803_34

def body803_36 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body803_35

def body803_37 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body803_36

def body803_38 : Prog (BitVec 64) :=
.seq body803_6 body803_7

def body803_39 : Prog (BitVec 64) :=
.seq body803_38 body803_5

def body803_40 : Prog (BitVec 64) :=
.seq body803_39 body803_8

def body803_41 : Prog (BitVec 64) :=
.seq body803_40 body803_6

def body803_42 : Prog (BitVec 64) :=
.seq body803_41 body803_9

def body803_43 : Prog (BitVec 64) :=
.seq body803_42 body803_10

def body803_44 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g1_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body803_43

def body803_45 : Prog (BitVec 64) :=
.seq body803_5 body803_44

def body803_46 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g1_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) body803_45

def body803_47 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 384#64]]) body803_46

def body803_48 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) body803_47

def body803_49 : Prog (BitVec 64) :=
.seq body803_48 body803_22

def body803_50 : Prog (BitVec 64) :=
.seq body803_23 body803_24

def body803_51 : Prog (BitVec 64) :=
.seq body803_50 body803_1

def body803_52 : Prog (BitVec 64) :=
.seq body803_51 body803_25

def body803_53 : Prog (BitVec 64) :=
.decCall ("one") (Flapjack.Shape.one) ("fp12_is_one") ([Flapjack.Exp.var Flapjack.VarKind.local "acc"]) body803_52

def body803_54 : Prog (BitVec 64) :=
.seq body803_49 body803_53

def body803_55 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body803_54

def body803_56 : Prog (BitVec 64) :=
.seq body803_0 body803_55

def body803_57 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 576#64]) body803_56

def body803_58 : Prog (BitVec 64) :=
.decCall ("q") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body803_57

def body803_59 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body803_58

def body803_60 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body803_59

def originalData803 : Decl (BitVec 64) :=
.function { name := "bls_pairing_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body803_37, returnShape := (Flapjack.Shape.one) }
def simplifiedData803 : Decl (BitVec 64) :=
.function { name := "bls_pairing_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body803_60, returnShape := (Flapjack.Shape.one) }
def original803 := Pancake.PanLang.declToHOL originalData803
def simplified803 := Pancake.PanLang.declToHOL simplifiedData803
end InitECandidate.Proofs.FrontendStages.Declarations
