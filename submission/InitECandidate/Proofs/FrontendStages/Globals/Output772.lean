import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data772
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate756
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody772_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def globalBody772_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody772_2 : Prog (BitVec 64) :=
.seq globalBody772_0 globalBody772_1

def globalBody772_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody772_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i1") (Flapjack.Exp.const 1#64)) globalBody772_2 globalBody772_3

def globalBody772_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def globalBody772_6 : Prog (BitVec 64) :=
.seq globalBody772_5 globalBody772_1

def globalBody772_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "i2") (Flapjack.Exp.const 1#64)) globalBody772_6 globalBody772_3

def globalBody772_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 192#64]]

def globalBody772_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u2",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 192#64]]

def globalBody772_10 : Prog (BitVec 64) :=
.seq globalBody772_8 globalBody772_9

def globalBody772_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "p2",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 192#64]]

def globalBody772_12 : Prog (BitVec 64) :=
.seq globalBody772_10 globalBody772_11

def globalBody772_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v2", Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 192#64]]

def globalBody772_14 : Prog (BitVec 64) :=
.seq globalBody772_12 globalBody772_13

def globalBody772_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody772_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_double"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def globalBody772_17 : Prog (BitVec 64) :=
.seq globalBody772_16 globalBody772_1

def globalBody772_18 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ueq") (Flapjack.Exp.const 1#64)) globalBody772_17 globalBody772_3

def globalBody772_19 : Prog (BitVec 64) :=
.seq globalBody772_15 globalBody772_18

def globalBody772_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_set_inf" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody772_21 : Prog (BitVec 64) :=
.seq globalBody772_19 globalBody772_20

def globalBody772_22 : Prog (BitVec 64) :=
.seq globalBody772_21 globalBody772_1

def globalBody772_23 : Prog (BitVec 64) :=
.decCall ("ueq") (Flapjack.Shape.one) ("fp2_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u2"]) globalBody772_22

def globalBody772_24 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "veq") (Flapjack.Exp.const 1#64)) globalBody772_23 globalBody772_3

def globalBody772_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u1",
    Flapjack.Exp.var Flapjack.VarKind.local "u2"]

def globalBody772_26 : Prog (BitVec 64) :=
.seq globalBody772_24 globalBody772_25

def globalBody772_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "v", Flapjack.Exp.var Flapjack.VarKind.local "v1",
    Flapjack.Exp.var Flapjack.VarKind.local "v2"]

def globalBody772_28 : Prog (BitVec 64) :=
.seq globalBody772_26 globalBody772_27

def globalBody772_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "vv", Flapjack.Exp.var Flapjack.VarKind.local "v"]

def globalBody772_30 : Prog (BitVec 64) :=
.seq globalBody772_28 globalBody772_29

def globalBody772_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "vvv2", Flapjack.Exp.var Flapjack.VarKind.local "vv",
    Flapjack.Exp.var Flapjack.VarKind.local "v2"]

def globalBody772_32 : Prog (BitVec 64) :=
.seq globalBody772_30 globalBody772_31

def globalBody772_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "v3", Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.var Flapjack.VarKind.local "vv"]

def globalBody772_34 : Prog (BitVec 64) :=
.seq globalBody772_32 globalBody772_33

def globalBody772_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p2", Flapjack.Exp.const 192#64]]

def globalBody772_36 : Prog (BitVec 64) :=
.seq globalBody772_34 globalBody772_35

def globalBody772_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody772_38 : Prog (BitVec 64) :=
.seq globalBody772_36 globalBody772_37

def globalBody772_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody772_40 : Prog (BitVec 64) :=
.seq globalBody772_38 globalBody772_39

def globalBody772_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "v3"]

def globalBody772_42 : Prog (BitVec 64) :=
.seq globalBody772_40 globalBody772_41

def globalBody772_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "vvv2",
    Flapjack.Exp.var Flapjack.VarKind.local "vvv2"]

def globalBody772_44 : Prog (BitVec 64) :=
.seq globalBody772_42 globalBody772_43

def globalBody772_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "q"]

def globalBody772_46 : Prog (BitVec 64) :=
.seq globalBody772_44 globalBody772_45

def globalBody772_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "q", Flapjack.Exp.var Flapjack.VarKind.local "v",
    Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody772_48 : Prog (BitVec 64) :=
.seq globalBody772_46 globalBody772_47

def globalBody772_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "vvv2",
    Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody772_50 : Prog (BitVec 64) :=
.seq globalBody772_48 globalBody772_49

def globalBody772_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "u1"]

def globalBody772_52 : Prog (BitVec 64) :=
.seq globalBody772_50 globalBody772_51

def globalBody772_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u2", Flapjack.Exp.var Flapjack.VarKind.local "v3",
    Flapjack.Exp.var Flapjack.VarKind.local "u2"]

def globalBody772_54 : Prog (BitVec 64) :=
.seq globalBody772_52 globalBody772_53

def globalBody772_55 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "u1", Flapjack.Exp.var Flapjack.VarKind.local "u1",
    Flapjack.Exp.var Flapjack.VarKind.local "u2"]

def globalBody772_56 : Prog (BitVec 64) :=
.seq globalBody772_54 globalBody772_55

def globalBody772_57 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "v3",
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody772_58 : Prog (BitVec 64) :=
.seq globalBody772_56 globalBody772_57

def globalBody772_59 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "q"]

def globalBody772_60 : Prog (BitVec 64) :=
.seq globalBody772_58 globalBody772_59

def globalBody772_61 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "u1"]

def globalBody772_62 : Prog (BitVec 64) :=
.seq globalBody772_60 globalBody772_61

def globalBody772_63 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "w"]

def globalBody772_64 : Prog (BitVec 64) :=
.seq globalBody772_62 globalBody772_63

def globalBody772_65 : Prog (BitVec 64) :=
.seq globalBody772_64 globalBody772_15

def globalBody772_66 : Prog (BitVec 64) :=
.seq globalBody772_65 globalBody772_1

def globalBody772_67 : Prog (BitVec 64) :=
.decCall ("veq") (Flapjack.Shape.one) ("fp2_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "v1", Flapjack.Exp.var Flapjack.VarKind.local "v2"]) globalBody772_66

def globalBody772_68 : Prog (BitVec 64) :=
.seq globalBody772_14 globalBody772_67

def globalBody772_69 : Prog (BitVec 64) :=
.dec ("q") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1056#64]) globalBody772_68

def globalBody772_70 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 960#64]) globalBody772_69

def globalBody772_71 : Prog (BitVec 64) :=
.dec ("w") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 864#64]) globalBody772_70

def globalBody772_72 : Prog (BitVec 64) :=
.dec ("v3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 768#64]) globalBody772_71

def globalBody772_73 : Prog (BitVec 64) :=
.dec ("vvv2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) globalBody772_72

def globalBody772_74 : Prog (BitVec 64) :=
.dec ("vv") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) globalBody772_73

def globalBody772_75 : Prog (BitVec 64) :=
.dec ("v") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) globalBody772_74

def globalBody772_76 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) globalBody772_75

def globalBody772_77 : Prog (BitVec 64) :=
.dec ("v2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) globalBody772_76

def globalBody772_78 : Prog (BitVec 64) :=
.dec ("v1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) globalBody772_77

def globalBody772_79 : Prog (BitVec 64) :=
.dec ("u2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) globalBody772_78

def globalBody772_80 : Prog (BitVec 64) :=
.dec ("u1") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") globalBody772_79

def globalBody772_81 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 12#64]]) globalBody772_80

def globalBody772_82 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody772_81

def globalBody772_83 : Prog (BitVec 64) :=
.seq globalBody772_7 globalBody772_82

def globalBody772_84 : Prog (BitVec 64) :=
.decCall ("i2") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "p2"]) globalBody772_83

def globalBody772_85 : Prog (BitVec 64) :=
.seq globalBody772_4 globalBody772_84

def globalBody772_86 : Prog (BitVec 64) :=
.decCall ("i1") (Flapjack.Shape.one) ("g2_is_inf") ([Flapjack.Exp.var Flapjack.VarKind.local "p1"]) globalBody772_85

def globalData772 : Decl (BitVec 64) :=
.function { name := "g2_add", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p1", Flapjack.Shape.one), ("p2", Flapjack.Shape.one)], body := globalBody772_86, returnShape := (Flapjack.Shape.one) }
def globalOutput772 := Pancake.PanLang.declToHOL globalData772
end InitECandidate.Proofs.FrontendStages.Declarations
