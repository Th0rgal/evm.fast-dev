import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data760
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate744
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody760_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def globalBody760_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody760_2 : Prog (BitVec 64) :=
.seq globalBody760_0 globalBody760_1

def globalBody760_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody760_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i1") (Flapjack.Exp.const 1#64)) globalBody760_2 globalBody760_3

def globalBody760_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def globalBody760_6 : Prog (BitVec 64) :=
.seq globalBody760_5 globalBody760_1

def globalBody760_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i2") (Flapjack.Exp.const 1#64)) globalBody760_6 globalBody760_3

def globalBody760_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def globalBody760_9 : Prog (BitVec 64) :=
.seq globalBody760_8 globalBody760_1

def globalBody760_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ueq") (Flapjack.Exp.const 1#64)) globalBody760_9 globalBody760_3

def globalBody760_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody760_12 : Prog (BitVec 64) :=
.seq globalBody760_10 globalBody760_11

def globalBody760_13 : Prog (BitVec 64) :=
.seq globalBody760_12 globalBody760_1

def globalBody760_14 : Prog (BitVec 64) :=
.decCall ("ueq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u2"]) globalBody760_13

def globalBody760_15 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "veq") (Flapjack.Exp.const 1#64)) globalBody760_14 globalBody760_3

def globalBody760_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody760_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "v3"]

def globalBody760_18 : Prog (BitVec 64) :=
.seq globalBody760_16 globalBody760_17

def globalBody760_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "a"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def globalBody760_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ny"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "ny"]

def globalBody760_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "t"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v3", Flapjack.Exp.var Flapjack.VarKind.local "u2"]

def globalBody760_22 : Prog (BitVec 64) :=
.seq globalBody760_20 globalBody760_21

def globalBody760_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ny"), none)) "bls_fp_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ny", Flapjack.Exp.var Flapjack.VarKind.local "t"]

def globalBody760_24 : Prog (BitVec 64) :=
.seq globalBody760_22 globalBody760_23

def globalBody760_25 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "nx")

def globalBody760_26 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ny")

def globalBody760_27 : Prog (BitVec 64) :=
.seq globalBody760_25 globalBody760_26

def globalBody760_28 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "nz")

def globalBody760_29 : Prog (BitVec 64) :=
.seq globalBody760_27 globalBody760_28

def globalBody760_30 : Prog (BitVec 64) :=
.seq globalBody760_29 globalBody760_1

def globalBody760_31 : Prog (BitVec 64) :=
.decCall ("nz") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v3", Flapjack.Exp.var Flapjack.VarKind.local "w"]) globalBody760_30

def globalBody760_32 : Prog (BitVec 64) :=
.seq globalBody760_24 globalBody760_31

def globalBody760_33 : Prog (BitVec 64) :=
.decCall ("ny") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "vvv2", Flapjack.Exp.var Flapjack.VarKind.local "a"]) globalBody760_32

def globalBody760_34 : Prog (BitVec 64) :=
.decCall ("nx") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "a"]) globalBody760_33

def globalBody760_35 : Prog (BitVec 64) :=
.seq globalBody760_19 globalBody760_34

def globalBody760_36 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_add") ([Flapjack.Exp.var Flapjack.VarKind.local "vvv2", Flapjack.Exp.var Flapjack.VarKind.local "vvv2"]) globalBody760_35

def globalBody760_37 : Prog (BitVec 64) :=
.seq globalBody760_18 globalBody760_36

def globalBody760_38 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "u"]) globalBody760_37

def globalBody760_39 : Prog (BitVec 64) :=
.decCall ("w") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) globalBody760_38

def globalBody760_40 : Prog (BitVec 64) :=
.decCall ("v3") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "vv"]) globalBody760_39

def globalBody760_41 : Prog (BitVec 64) :=
.decCall ("vvv2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "vv", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) globalBody760_40

def globalBody760_42 : Prog (BitVec 64) :=
.decCall ("vv") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sqr") ([Flapjack.Exp.var Flapjack.VarKind.local "v"]) globalBody760_41

def globalBody760_43 : Prog (BitVec 64) :=
.decCall ("v") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) globalBody760_42

def globalBody760_44 : Prog (BitVec 64) :=
.decCall ("u") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_sub") ([Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u2"]) globalBody760_43

def globalBody760_45 : Prog (BitVec 64) :=
.seq globalBody760_15 globalBody760_44

def globalBody760_46 : Prog (BitVec 64) :=
.decCall ("veq") (Flapjack.Shape.one) ("bls_fp_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) globalBody760_45

def globalBody760_47 : Prog (BitVec 64) :=
.decCall ("v2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) globalBody760_46

def globalBody760_48 : Prog (BitVec 64) :=
.decCall ("v1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]) globalBody760_47

def globalBody760_49 : Prog (BitVec 64) :=
.decCall ("u2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]) globalBody760_48

def globalBody760_50 : Prog (BitVec 64) :=
.decCall ("u1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "y2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]) globalBody760_49

def globalBody760_51 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 48#64])) globalBody760_50

def globalBody760_52 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p2")) globalBody760_51

def globalBody760_53 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 48#64])) globalBody760_52

def globalBody760_54 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p1")) globalBody760_53

def globalBody760_55 : Prog (BitVec 64) :=
.seq globalBody760_7 globalBody760_54

def globalBody760_56 : Prog (BitVec 64) :=
.decCall ("i2") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z2"]) globalBody760_55

def globalBody760_57 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 96#64])) globalBody760_56

def globalBody760_58 : Prog (BitVec 64) :=
.seq globalBody760_4 globalBody760_57

def globalBody760_59 : Prog (BitVec 64) :=
.decCall ("i1") (Flapjack.Shape.one) ("bls_fp_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "z1"]) globalBody760_58

def globalBody760_60 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 96#64])) globalBody760_59

def globalData760 : Decl (BitVec 64) :=
.function { name := "g1_add", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p1", Flapjack.Shape.one), ("p2", Flapjack.Shape.one)], body := globalBody760_60, returnShape := (Flapjack.Shape.one) }
def globalOutput760 := Pancake.PanLang.declToHOL globalData760
end InitECandidate.Proofs.FrontendStages.Declarations
