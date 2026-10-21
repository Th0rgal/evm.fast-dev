import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data785
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate769
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody785_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "temp"), none)) "bls_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "zt2", Flapjack.Exp.var Flapjack.VarKind.local "temp"]

def globalBody785_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "den"), none)) "bls_fp_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody785_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "temp"), none)) "bls_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "temp", Flapjack.Exp.var Flapjack.VarKind.local "one"]

def globalBody785_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "den"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "zc", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody785_4 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody785_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "dz") (Flapjack.Exp.const 1#64)) globalBody785_3 globalBody785_4

def globalBody785_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "u"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def globalBody785_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "den2"]

def globalBody785_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "u"), none)) "bls_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody785_9 : Prog (BitVec 64) :=
.seq globalBody785_7 globalBody785_8

def globalBody785_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "w"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody785_11 : Prog (BitVec 64) :=
.seq globalBody785_9 globalBody785_10

def globalBody785_12 : Prog (BitVec 64) :=
.seq globalBody785_11 globalBody785_8

def globalBody785_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "t3"]

def globalBody785_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "c"]

def globalBody785_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "num"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "num", Flapjack.Exp.var Flapjack.VarKind.local "zt2"]

def globalBody785_16 : Prog (BitVec 64) :=
.seq globalBody785_14 globalBody785_15

def globalBody785_17 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
      Flapjack.Exp.const 1856#64])) globalBody785_16

def globalBody785_18 : Prog (BitVec 64) :=
.seq globalBody785_13 globalBody785_17

def globalBody785_19 : Prog (BitVec 64) :=
.decCall ("t3") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody785_18

def globalBody785_20 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "sq"))
  (Flapjack.Exp.const 0#64)) globalBody785_19 globalBody785_4

def globalBody785_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_neg"
  [Flapjack.Exp.var Flapjack.VarKind.local "y"]

def globalBody785_22 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "st_")
  (Flapjack.Exp.var Flapjack.VarKind.local "sy")) globalBody785_21 globalBody785_4

def globalBody785_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "den"]

def globalBody785_24 : Prog (BitVec 64) :=
.seq globalBody785_22 globalBody785_23

def globalBody785_25 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "num")

def globalBody785_26 : Prog (BitVec 64) :=
.seq globalBody785_24 globalBody785_25

def globalBody785_27 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y")

def globalBody785_28 : Prog (BitVec 64) :=
.seq globalBody785_26 globalBody785_27

def globalBody785_29 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "den")

def globalBody785_30 : Prog (BitVec 64) :=
.seq globalBody785_28 globalBody785_29

def globalBody785_31 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody785_32 : Prog (BitVec 64) :=
.seq globalBody785_30 globalBody785_31

def globalBody785_33 : Prog (BitVec 64) :=
.decCall ("sy") (Flapjack.Shape.one) ("bls_fp_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) globalBody785_32

def globalBody785_34 : Prog (BitVec 64) :=
.decCall ("st_") (Flapjack.Shape.one) ("bls_fp_sgn0") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody785_33

def globalBody785_35 : Prog (BitVec 64) :=
.seq globalBody785_20 globalBody785_34

def globalBody785_36 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "sq"),
    Flapjack.Exp.rField 6 (Flapjack.Exp.var Flapjack.VarKind.local "sq")]) globalBody785_35

def globalBody785_37 : Prog (BitVec 64) :=
.decCall ("sq") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("swu_sqrt_division_fp") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody785_36

def globalBody785_38 : Prog (BitVec 64) :=
.seq globalBody785_12 globalBody785_37

def globalBody785_39 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "num"]) globalBody785_38

def globalBody785_40 : Prog (BitVec 64) :=
.seq globalBody785_6 globalBody785_39

def globalBody785_41 : Prog (BitVec 64) :=
.decCall ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "num"]) globalBody785_40

def globalBody785_42 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "den2", Flapjack.Exp.var Flapjack.VarKind.local "den"]) globalBody785_41

def globalBody785_43 : Prog (BitVec 64) :=
.decCall ("den2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) globalBody785_42

def globalBody785_44 : Prog (BitVec 64) :=
.seq globalBody785_5 globalBody785_43

def globalBody785_45 : Prog (BitVec 64) :=
.decCall ("dz") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "den"]) globalBody785_44

def globalBody785_46 : Prog (BitVec 64) :=
.decCall ("num") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "temp"]) globalBody785_45

def globalBody785_47 : Prog (BitVec 64) :=
.seq globalBody785_2 globalBody785_46

def globalBody785_48 : Prog (BitVec 64) :=
.dec ("one") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 8505329371266088957#64, Flapjack.Exp.const 17002214543764226050#64,
    Flapjack.Exp.const 6865905132761471162#64, Flapjack.Exp.const 8632934651105793861#64,
    Flapjack.Exp.const 6631298214892334189#64, Flapjack.Exp.const 1582556514881692819#64]) globalBody785_47

def globalBody785_49 : Prog (BitVec 64) :=
.seq globalBody785_1 globalBody785_48

def globalBody785_50 : Prog (BitVec 64) :=
.decCall ("den") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "temp"]) globalBody785_49

def globalBody785_51 : Prog (BitVec 64) :=
.seq globalBody785_0 globalBody785_50

def globalBody785_52 : Prog (BitVec 64) :=
.decCall ("temp") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "zt2"]) globalBody785_51

def globalBody785_53 : Prog (BitVec 64) :=
.decCall ("zt2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "zc", Flapjack.Exp.var Flapjack.VarKind.local "t2"]) globalBody785_52

def globalBody785_54 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) globalBody785_53

def globalBody785_55 : Prog (BitVec 64) :=
.dec ("zc") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
      Flapjack.Exp.const 1808#64])) globalBody785_54

def globalBody785_56 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
      Flapjack.Exp.const 1760#64])) globalBody785_55

def globalBody785_57 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 392#64]),
      Flapjack.Exp.const 1712#64])) globalBody785_56

def globalData785 : Decl (BitVec 64) :=
.function { name := "swu_g1", inline := false, exported := false, params := [("r", Flapjack.Shape.one),
  ("t",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := globalBody785_57, returnShape := (Flapjack.Shape.one) }
def globalOutput785 := Pancake.PanLang.declToHOL globalData785
end InitECandidate.Proofs.FrontendStages.Declarations
