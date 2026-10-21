import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data636
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate620
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody636_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody636_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody636_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "zz") (Flapjack.Exp.const 1#64)) globalBody636_0 globalBody636_1

def globalBody636_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "p256_set_infinity" [Flapjack.Exp.var Flapjack.VarKind.local "pt"]

def globalBody636_4 : Prog (BitVec 64) :=
.seq globalBody636_3 globalBody636_0

def globalBody636_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "yz") (Flapjack.Exp.const 1#64)) globalBody636_4 globalBody636_1

def globalBody636_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "alpha"), none)) "p256_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "alpha2", Flapjack.Exp.var Flapjack.VarKind.local "alpha"]

def globalBody636_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "b4"), none)) "p256_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "b4", Flapjack.Exp.var Flapjack.VarKind.local "b4"]

def globalBody636_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "x3"), none)) "p256_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "x3", Flapjack.Exp.var Flapjack.VarKind.local "b8"]

def globalBody636_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z3"), none)) "p256_fp_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "z3"]

def globalBody636_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z3"), none)) "p256_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "z3", Flapjack.Exp.var Flapjack.VarKind.local "gamma"]

def globalBody636_11 : Prog (BitVec 64) :=
.seq globalBody636_9 globalBody636_10

def globalBody636_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "z3"), none)) "p256_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "z3", Flapjack.Exp.var Flapjack.VarKind.local "delta"]

def globalBody636_13 : Prog (BitVec 64) :=
.seq globalBody636_11 globalBody636_12

def globalBody636_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y3"), none)) "p256_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "alpha", Flapjack.Exp.var Flapjack.VarKind.local "y3"]

def globalBody636_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "g2"), none)) "p256_fp_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "g2", Flapjack.Exp.var Flapjack.VarKind.local "g2"]

def globalBody636_16 : Prog (BitVec 64) :=
.seq globalBody636_15 globalBody636_15

def globalBody636_17 : Prog (BitVec 64) :=
.seq globalBody636_16 globalBody636_15

def globalBody636_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "y3"), none)) "p256_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "y3", Flapjack.Exp.var Flapjack.VarKind.local "g2"]

def globalBody636_19 : Prog (BitVec 64) :=
.seq globalBody636_17 globalBody636_18

def globalBody636_20 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "pt") (Flapjack.Exp.var Flapjack.VarKind.local "x3")

def globalBody636_21 : Prog (BitVec 64) :=
.seq globalBody636_19 globalBody636_20

def globalBody636_22 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 32#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "y3")

def globalBody636_23 : Prog (BitVec 64) :=
.seq globalBody636_21 globalBody636_22

def globalBody636_24 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "z3")

def globalBody636_25 : Prog (BitVec 64) :=
.seq globalBody636_23 globalBody636_24

def globalBody636_26 : Prog (BitVec 64) :=
.seq globalBody636_25 globalBody636_0

def globalBody636_27 : Prog (BitVec 64) :=
.decCall ("g2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "gamma"]) globalBody636_26

def globalBody636_28 : Prog (BitVec 64) :=
.seq globalBody636_14 globalBody636_27

def globalBody636_29 : Prog (BitVec 64) :=
.decCall ("y3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "b4", Flapjack.Exp.var Flapjack.VarKind.local "x3"]) globalBody636_28

def globalBody636_30 : Prog (BitVec 64) :=
.seq globalBody636_13 globalBody636_29

def globalBody636_31 : Prog (BitVec 64) :=
.decCall ("z3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "z"]) globalBody636_30

def globalBody636_32 : Prog (BitVec 64) :=
.seq globalBody636_8 globalBody636_31

def globalBody636_33 : Prog (BitVec 64) :=
.decCall ("b8") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "b4", Flapjack.Exp.var Flapjack.VarKind.local "b4"]) globalBody636_32

def globalBody636_34 : Prog (BitVec 64) :=
.seq globalBody636_7 globalBody636_33

def globalBody636_35 : Prog (BitVec 64) :=
.decCall ("b4") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "beta", Flapjack.Exp.var Flapjack.VarKind.local "beta"]) globalBody636_34

def globalBody636_36 : Prog (BitVec 64) :=
.decCall ("x3") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "alpha"]) globalBody636_35

def globalBody636_37 : Prog (BitVec 64) :=
.seq globalBody636_6 globalBody636_36

def globalBody636_38 : Prog (BitVec 64) :=
.decCall ("alpha2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "alpha", Flapjack.Exp.var Flapjack.VarKind.local "alpha"]) globalBody636_37

def globalBody636_39 : Prog (BitVec 64) :=
.decCall ("alpha") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2"]) globalBody636_38

def globalBody636_40 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "delta"]) globalBody636_39

def globalBody636_41 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "delta"]) globalBody636_40

def globalBody636_42 : Prog (BitVec 64) :=
.decCall ("beta") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "gamma"]) globalBody636_41

def globalBody636_43 : Prog (BitVec 64) :=
.decCall ("gamma") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) globalBody636_42

def globalBody636_44 : Prog (BitVec 64) :=
.decCall ("delta") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("p256_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) globalBody636_43

def globalBody636_45 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "pt")) globalBody636_44

def globalBody636_46 : Prog (BitVec 64) :=
.seq globalBody636_5 globalBody636_45

def globalBody636_47 : Prog (BitVec 64) :=
.decCall ("yz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "y"]) globalBody636_46

def globalBody636_48 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 32#64])) globalBody636_47

def globalBody636_49 : Prog (BitVec 64) :=
.seq globalBody636_2 globalBody636_48

def globalBody636_50 : Prog (BitVec 64) :=
.decCall ("zz") (Flapjack.Shape.one) ("u256_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z"]) globalBody636_49

def globalBody636_51 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) (Flapjack.Exp.load (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.const 64#64])) globalBody636_50

def globalData636 : Decl (BitVec 64) :=
.function { name := "p256_ec_double", inline := false, exported := false, params := [("pt", Flapjack.Shape.one)], body := globalBody636_51, returnShape := (Flapjack.Shape.one) }
def globalOutput636 := Pancake.PanLang.declToHOL globalData636
end InitECandidate.Proofs.FrontendStages.Declarations
