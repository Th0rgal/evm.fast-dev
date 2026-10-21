import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify786
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body802_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body802_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body802_2 : Prog (BitVec 64) :=
.seq body802_0 body802_1

def body802_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body802_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body802_2 body802_3

def body802_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sg") (Flapjack.Exp.const 0#64)) body802_2 body802_3

def body802_6 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "s") (Flapjack.Exp.var Flapjack.VarKind.local "m")

def body802_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 4#64]

def body802_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body802_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body802_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 0#64)) body802_8 body802_9

def body802_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body802_12 : Prog (BitVec 64) :=
.seq body802_10 body802_11

def body802_13 : Prog (BitVec 64) :=
.seq body802_7 body802_12

def body802_14 : Prog (BitVec 64) :=
.seq body802_6 body802_13

def body802_15 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 256#64],
  Flapjack.Exp.const 32#64]) body802_14

def body802_16 : Prog (BitVec 64) :=
.seq body802_5 body802_15

def body802_17 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g2_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body802_16

def body802_18 : Prog (BitVec 64) :=
.seq body802_4 body802_17

def body802_19 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g2_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) body802_18

def body802_20 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 288#64]]) body802_19

def body802_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) body802_20

def body802_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body802_23 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body802_24 : Prog (BitVec 64) :=
.seq body802_0 body802_23

def body802_25 : Prog (BitVec 64) :=
.seq body802_22 body802_24

def body802_26 : Prog (BitVec 64) :=
.seq body802_21 body802_25

def body802_27 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body802_26

def body802_28 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body802_27

def body802_29 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body802_28

def body802_30 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body802_29

def body802_31 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body802_30

def body802_32 : Prog (BitVec 64) :=
.seq body802_6 body802_7

def body802_33 : Prog (BitVec 64) :=
.seq body802_32 body802_10

def body802_34 : Prog (BitVec 64) :=
.seq body802_33 body802_11

def body802_35 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 256#64],
  Flapjack.Exp.const 32#64]) body802_34

def body802_36 : Prog (BitVec 64) :=
.seq body802_5 body802_35

def body802_37 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g2_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body802_36

def body802_38 : Prog (BitVec 64) :=
.seq body802_4 body802_37

def body802_39 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g2_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) body802_38

def body802_40 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 288#64]]) body802_39

def body802_41 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) body802_40

def body802_42 : Prog (BitVec 64) :=
.seq body802_41 body802_22

def body802_43 : Prog (BitVec 64) :=
.seq body802_42 body802_0

def body802_44 : Prog (BitVec 64) :=
.seq body802_43 body802_23

def body802_45 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body802_44

def body802_46 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body802_45

def body802_47 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body802_46

def body802_48 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body802_47

def body802_49 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body802_48

def originalData802 : Decl (BitVec 64) :=
.function { name := "bls_g2_msm_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body802_31, returnShape := (Flapjack.Shape.one) }
def simplifiedData802 : Decl (BitVec 64) :=
.function { name := "bls_g2_msm_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body802_49, returnShape := (Flapjack.Shape.one) }
def original802 := Pancake.PanLang.declToHOL originalData802
def simplified802 := Pancake.PanLang.declToHOL simplifiedData802
end InitECandidate.Proofs.FrontendStages.Declarations
