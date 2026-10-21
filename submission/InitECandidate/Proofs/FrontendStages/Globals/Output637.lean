import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data637
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate621
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody637_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_set_affine"
  [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.var Flapjack.VarKind.local "ax",
    Flapjack.Exp.var Flapjack.VarKind.local "ay"]

def globalBody637_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody637_2 : Prog (BitVec 64) :=
.seq globalBody637_0 globalBody637_1

def globalBody637_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody637_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "zz") (Flapjack.Exp.const 1#64)) globalBody637_2 globalBody637_3

def globalBody637_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "s2"), none)) "p256_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "ay", Flapjack.Exp.var Flapjack.VarKind.local "s2"]

def globalBody637_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_set_infinity" [Flapjack.Exp.var Flapjack.VarKind.local "pt"]

def globalBody637_7 : Prog (BitVec 64) :=
.seq globalBody637_6 globalBody637_1

def globalBody637_8 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ysz") (Flapjack.Exp.const 1#64)) globalBody637_7 globalBody637_3

def globalBody637_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_ec_double" [Flapjack.Exp.var Flapjack.VarKind.local "pt"]

def globalBody637_10 : Prog (BitVec 64) :=
.seq globalBody637_8 globalBody637_9

def globalBody637_11 : Prog (BitVec 64) :=
.seq globalBody637_10 globalBody637_1

def globalBody637_12 : Prog (BitVec 64) :=
.decCall ("ysz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "ysum"]) globalBody637_11

def globalBody637_13 : Prog (BitVec 64) :=
.decCall ("ysum") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "s2", Flapjack.Exp.var Flapjack.VarKind.local "y1"]) globalBody637_12

def globalBody637_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "samex") (Flapjack.Exp.const 1#64)) globalBody637_13 globalBody637_3

def globalBody637_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x3"), none)) "p256_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "x3", Flapjack.Exp.var Flapjack.VarKind.local "hhh"]

def globalBody637_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x3"), none)) "p256_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "x3", Flapjack.Exp.var Flapjack.VarKind.local "v2"]

def globalBody637_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y3"), none)) "p256_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "rr", Flapjack.Exp.var Flapjack.VarKind.local "y3"]

def globalBody637_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y3"), none)) "p256_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "y3", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def globalBody637_19 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pt") (Flapjack.Exp.var Flapjack.VarKind.local "x3")

def globalBody637_20 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y3")

def globalBody637_21 : Prog (BitVec 64) :=
.seq globalBody637_19 globalBody637_20

def globalBody637_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "z3")

def globalBody637_23 : Prog (BitVec 64) :=
.seq globalBody637_21 globalBody637_22

def globalBody637_24 : Prog (BitVec 64) :=
.seq globalBody637_23 globalBody637_1

def globalBody637_25 : Prog (BitVec 64) :=
.decCall ("z3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "h"]) globalBody637_24

def globalBody637_26 : Prog (BitVec 64) :=
.seq globalBody637_18 globalBody637_25

def globalBody637_27 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "hhh"]) globalBody637_26

def globalBody637_28 : Prog (BitVec 64) :=
.seq globalBody637_17 globalBody637_27

def globalBody637_29 : Prog (BitVec 64) :=
.decCall ("y3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "x3"]) globalBody637_28

def globalBody637_30 : Prog (BitVec 64) :=
.seq globalBody637_16 globalBody637_29

def globalBody637_31 : Prog (BitVec 64) :=
.decCall ("v2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody637_30

def globalBody637_32 : Prog (BitVec 64) :=
.seq globalBody637_15 globalBody637_31

def globalBody637_33 : Prog (BitVec 64) :=
.decCall ("x3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "rr"]) globalBody637_32

def globalBody637_34 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "hh"]) globalBody637_33

def globalBody637_35 : Prog (BitVec 64) :=
.decCall ("hhh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "h", Flapjack.Exp.var Flapjack.VarKind.local "hh"]) globalBody637_34

def globalBody637_36 : Prog (BitVec 64) :=
.decCall ("hh") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "h"]) globalBody637_35

def globalBody637_37 : Prog (BitVec 64) :=
.decCall ("rr") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "s2", Flapjack.Exp.var Flapjack.VarKind.local "y1"]) globalBody637_36

def globalBody637_38 : Prog (BitVec 64) :=
.decCall ("h") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "u2", Flapjack.Exp.var Flapjack.VarKind.local "x1"]) globalBody637_37

def globalBody637_39 : Prog (BitVec 64) :=
.seq globalBody637_14 globalBody637_38

def globalBody637_40 : Prog (BitVec 64) :=
.decCall ("samex") (Flapjack.Shape.one) ("u256_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "u2", Flapjack.Exp.var Flapjack.VarKind.local "x1"]) globalBody637_39

def globalBody637_41 : Prog (BitVec 64) :=
.seq globalBody637_5 globalBody637_40

def globalBody637_42 : Prog (BitVec 64) :=
.decCall ("s2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "z1z1"]) globalBody637_41

def globalBody637_43 : Prog (BitVec 64) :=
.decCall ("u2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "ax", Flapjack.Exp.var Flapjack.VarKind.local "z1z1"]) globalBody637_42

def globalBody637_44 : Prog (BitVec 64) :=
.decCall ("z1z1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "z1"]) globalBody637_43

def globalBody637_45 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 32#64])) globalBody637_44

def globalBody637_46 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pt")) globalBody637_45

def globalBody637_47 : Prog (BitVec 64) :=
.seq globalBody637_4 globalBody637_46

def globalBody637_48 : Prog (BitVec 64) :=
.decCall ("zz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z1"]) globalBody637_47

def globalBody637_49 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 64#64])) globalBody637_48

def globalData637 : Decl (BitVec 64) :=
.function { name := "p256_ec_add_affine", inline := false, exported := false, params := [("pt", Flapjack.Shape.one),
  ("ax", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]),
  ("ay", Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])], body := globalBody637_49, returnShape := (Flapjack.Shape.one) }
def globalOutput637 := Pancake.PanLang.declToHOL globalData637
end InitECandidate.Proofs.FrontendStages.Declarations
