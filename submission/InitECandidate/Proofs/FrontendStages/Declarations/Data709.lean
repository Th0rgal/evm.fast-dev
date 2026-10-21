import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify693
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body709_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
      Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64])

def body709_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body709_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "az") (Flapjack.Exp.const 1#64)) body709_0 body709_1

def body709_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "x1")

def body709_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "u"))
  (Flapjack.Exp.const 1#64)) body709_3 body709_1

def body709_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "u"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "u")])
  (Flapjack.Exp.const 0#64)) body709_4 body709_1

def body709_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "x2")

def body709_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"))
  (Flapjack.Exp.const 1#64)) body709_6 body709_1

def body709_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.or
    [Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "v"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "v")])
  (Flapjack.Exp.const 0#64)) body709_7 body709_1

def body709_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "u"), none)) "bls_fp_shr1"
  [Flapjack.Exp.var Flapjack.VarKind.local "u"]

def body709_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x1"), none)) "bls_fp_half_can"
  [Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def body709_11 : Prog (BitVec 64) :=
.seq body709_9 body709_10

def body709_12 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "u"), Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 0#64)) body709_11

def body709_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "v"), none)) "bls_fp_shr1"
  [Flapjack.Exp.var Flapjack.VarKind.local "v"]

def body709_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x2"), none)) "bls_fp_half_can"
  [Flapjack.Exp.var Flapjack.VarKind.local "x2"]

def body709_15 : Prog (BitVec 64) :=
.seq body709_13 body709_14

def body709_16 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.op Flapjack.BinOp.and
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "v"), Flapjack.Exp.const 1#64])
  (Flapjack.Exp.const 0#64)) body709_15

def body709_17 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "u"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "d"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "d")])

def body709_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x1"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "x2"]

def body709_19 : Prog (BitVec 64) :=
.seq body709_17 body709_18

def body709_20 : Prog (BitVec 64) :=
.decCall ("d") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("bls_fp_sub_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "v"]) body709_19

def body709_21 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "v"
  (Flapjack.Exp.rStruct
    [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 2 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 3 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 4 (Flapjack.Exp.var Flapjack.VarKind.local "e"),
      Flapjack.Exp.rField 5 (Flapjack.Exp.var Flapjack.VarKind.local "e")])

def body709_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x2"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def body709_23 : Prog (BitVec 64) :=
.seq body709_21 body709_22

def body709_24 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one, Flapjack.Shape.one]) ("bls_fp_sub_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "u"]) body709_23

def body709_25 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ult") (Flapjack.Exp.const 0#64)) body709_20 body709_24

def body709_26 : Prog (BitVec 64) :=
.decCall ("ult") (Flapjack.Shape.one) ("bls_fp_lt_raw") ([Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "v"]) body709_25

def body709_27 : Prog (BitVec 64) :=
.seq body709_16 body709_26

def body709_28 : Prog (BitVec 64) :=
.seq body709_12 body709_27

def body709_29 : Prog (BitVec 64) :=
.seq body709_8 body709_28

def body709_30 : Prog (BitVec 64) :=
.seq body709_5 body709_29

def body709_31 : Prog (BitVec 64) :=
.while (Flapjack.Exp.const 1#64) body709_30

def body709_32 : Prog (BitVec 64) :=
.seq body709_31 body709_0

def body709_33 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body709_32

def body709_34 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body709_33

def body709_35 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 13402431016077863595#64, Flapjack.Exp.const 2210141511517208575#64,
    Flapjack.Exp.const 7435674573564081700#64, Flapjack.Exp.const 7239337960414712511#64,
    Flapjack.Exp.const 5412103778470702295#64, Flapjack.Exp.const 1873798617647539866#64]) body709_34

def body709_36 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "a") body709_35

def body709_37 : Prog (BitVec 64) :=
.seq body709_2 body709_36

def body709_38 : Prog (BitVec 64) :=
.decCall ("az") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "a"]) body709_37

def body709_39 : Prog (BitVec 64) :=
.seq body709_5 body709_8

def body709_40 : Prog (BitVec 64) :=
.seq body709_39 body709_12

def body709_41 : Prog (BitVec 64) :=
.seq body709_40 body709_16

def body709_42 : Prog (BitVec 64) :=
.seq body709_41 body709_26

def body709_43 : Prog (BitVec 64) :=
.while (Flapjack.Exp.const 1#64) body709_42

def body709_44 : Prog (BitVec 64) :=
.seq body709_43 body709_0

def body709_45 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body709_44

def body709_46 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 1#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64,
    Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64]) body709_45

def body709_47 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.rStruct
  [Flapjack.Exp.const 13402431016077863595#64, Flapjack.Exp.const 2210141511517208575#64,
    Flapjack.Exp.const 7435674573564081700#64, Flapjack.Exp.const 7239337960414712511#64,
    Flapjack.Exp.const 5412103778470702295#64, Flapjack.Exp.const 1873798617647539866#64]) body709_46

def body709_48 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "a") body709_47

def body709_49 : Prog (BitVec 64) :=
.seq body709_2 body709_48

def body709_50 : Prog (BitVec 64) :=
.decCall ("az") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "a"]) body709_49

def originalData709 : Decl (BitVec 64) :=
.function { name := "bls_fp_inv_raw", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body709_38, returnShape := (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) }
def simplifiedData709 : Decl (BitVec 64) :=
.function { name := "bls_fp_inv_raw", inline := false, exported := false, params := [("a",
    Flapjack.Shape.comb
      [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
        Flapjack.Shape.one])], body := body709_50, returnShape := (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) }
def original709 := Pancake.PanLang.declToHOL originalData709
def simplified709 := Pancake.PanLang.declToHOL simplifiedData709
end InitECandidate.Proofs.FrontendStages.Declarations
