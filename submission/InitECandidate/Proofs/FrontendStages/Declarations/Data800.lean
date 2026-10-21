import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify784
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body800_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body800_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body800_2 : Prog (BitVec 64) :=
.seq body800_0 body800_1

def body800_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body800_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body800_2 body800_3

def body800_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sg") (Flapjack.Exp.const 0#64)) body800_2 body800_3

def body800_6 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "s") (Flapjack.Exp.var Flapjack.VarKind.local "m")

def body800_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "p",
    Flapjack.Exp.var Flapjack.VarKind.local "s", Flapjack.Exp.const 4#64]

def body800_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body800_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "acc",
    Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body800_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i") (Flapjack.Exp.const 0#64)) body800_8 body800_9

def body800_11 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body800_12 : Prog (BitVec 64) :=
.seq body800_10 body800_11

def body800_13 : Prog (BitVec 64) :=
.seq body800_7 body800_12

def body800_14 : Prog (BitVec 64) :=
.seq body800_6 body800_13

def body800_15 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 128#64],
  Flapjack.Exp.const 32#64]) body800_14

def body800_16 : Prog (BitVec 64) :=
.seq body800_5 body800_15

def body800_17 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g1_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body800_16

def body800_18 : Prog (BitVec 64) :=
.seq body800_4 body800_17

def body800_19 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g1_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) body800_18

def body800_20 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 160#64]]) body800_19

def body800_21 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) body800_20

def body800_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "acc", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body800_23 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body800_24 : Prog (BitVec 64) :=
.seq body800_0 body800_23

def body800_25 : Prog (BitVec 64) :=
.seq body800_22 body800_24

def body800_26 : Prog (BitVec 64) :=
.seq body800_21 body800_25

def body800_27 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body800_26

def body800_28 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body800_27

def body800_29 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body800_28

def body800_30 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body800_29

def body800_31 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body800_30

def body800_32 : Prog (BitVec 64) :=
.seq body800_6 body800_7

def body800_33 : Prog (BitVec 64) :=
.seq body800_32 body800_10

def body800_34 : Prog (BitVec 64) :=
.seq body800_33 body800_11

def body800_35 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("u256_from_be") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.const 128#64],
  Flapjack.Exp.const 32#64]) body800_34

def body800_36 : Prog (BitVec 64) :=
.seq body800_5 body800_35

def body800_37 : Prog (BitVec 64) :=
.decCall ("sg") (Flapjack.Shape.one) ("g1_subgroup_check") ([Flapjack.Exp.var Flapjack.VarKind.local "p"]) body800_36

def body800_38 : Prog (BitVec 64) :=
.seq body800_4 body800_37

def body800_39 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g1_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "p"]) body800_38

def body800_40 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "data",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 160#64]]) body800_39

def body800_41 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.less (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "k")) body800_40

def body800_42 : Prog (BitVec 64) :=
.seq body800_41 body800_22

def body800_43 : Prog (BitVec 64) :=
.seq body800_42 body800_0

def body800_44 : Prog (BitVec 64) :=
.seq body800_43 body800_23

def body800_45 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body800_44

def body800_46 : Prog (BitVec 64) :=
.decCall ("s") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 32#64]) body800_45

def body800_47 : Prog (BitVec 64) :=
.decCall ("p") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body800_46

def body800_48 : Prog (BitVec 64) :=
.decCall ("acc") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body800_47

def body800_49 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body800_48

def originalData800 : Decl (BitVec 64) :=
.function { name := "bls_g1_msm_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body800_31, returnShape := (Flapjack.Shape.one) }
def simplifiedData800 : Decl (BitVec 64) :=
.function { name := "bls_g1_msm_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("k", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body800_49, returnShape := (Flapjack.Shape.one) }
def original800 := Pancake.PanLang.declToHOL originalData800
def simplified800 := Pancake.PanLang.declToHOL simplifiedData800
end InitECandidate.Proofs.FrontendStages.Declarations
