import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data779
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate763
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody779_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp0", Flapjack.Exp.var Flapjack.VarKind.local "rx"]

def globalBody779_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp1", Flapjack.Exp.var Flapjack.VarKind.local "ry"]

def globalBody779_2 : Prog (BitVec 64) :=
.seq globalBody779_0 globalBody779_1

def globalBody779_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp2", Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def globalBody779_4 : Prog (BitVec 64) :=
.seq globalBody779_2 globalBody779_3

def globalBody779_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp1",
    Flapjack.Exp.var Flapjack.VarKind.local "rx"]

def globalBody779_6 : Prog (BitVec 64) :=
.seq globalBody779_4 globalBody779_5

def globalBody779_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def globalBody779_8 : Prog (BitVec 64) :=
.seq globalBody779_6 globalBody779_7

def globalBody779_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def globalBody779_10 : Prog (BitVec 64) :=
.seq globalBody779_8 globalBody779_9

def globalBody779_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp2"]

def globalBody779_12 : Prog (BitVec 64) :=
.seq globalBody779_10 globalBody779_11

def globalBody779_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def globalBody779_14 : Prog (BitVec 64) :=
.seq globalBody779_12 globalBody779_13

def globalBody779_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp4", Flapjack.Exp.var Flapjack.VarKind.local "tmp0",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def globalBody779_16 : Prog (BitVec 64) :=
.seq globalBody779_14 globalBody779_15

def globalBody779_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp4", Flapjack.Exp.var Flapjack.VarKind.local "tmp4",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def globalBody779_18 : Prog (BitVec 64) :=
.seq globalBody779_16 globalBody779_17

def globalBody779_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "rx",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp4"]

def globalBody779_20 : Prog (BitVec 64) :=
.seq globalBody779_18 globalBody779_19

def globalBody779_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp5", Flapjack.Exp.var Flapjack.VarKind.local "tmp4"]

def globalBody779_22 : Prog (BitVec 64) :=
.seq globalBody779_20 globalBody779_21

def globalBody779_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "zsq", Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def globalBody779_24 : Prog (BitVec 64) :=
.seq globalBody779_22 globalBody779_23

def globalBody779_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "nx", Flapjack.Exp.var Flapjack.VarKind.local "tmp5",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def globalBody779_26 : Prog (BitVec 64) :=
.seq globalBody779_24 globalBody779_25

def globalBody779_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "nx", Flapjack.Exp.var Flapjack.VarKind.local "nx",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def globalBody779_28 : Prog (BitVec 64) :=
.seq globalBody779_26 globalBody779_27

def globalBody779_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "ry"]

def globalBody779_30 : Prog (BitVec 64) :=
.seq globalBody779_28 globalBody779_29

def globalBody779_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz"]

def globalBody779_32 : Prog (BitVec 64) :=
.seq globalBody779_30 globalBody779_31

def globalBody779_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def globalBody779_34 : Prog (BitVec 64) :=
.seq globalBody779_32 globalBody779_33

def globalBody779_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "rz", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def globalBody779_36 : Prog (BitVec 64) :=
.seq globalBody779_34 globalBody779_35

def globalBody779_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ry", Flapjack.Exp.var Flapjack.VarKind.local "tmp3",
    Flapjack.Exp.var Flapjack.VarKind.local "nx"]

def globalBody779_38 : Prog (BitVec 64) :=
.seq globalBody779_36 globalBody779_37

def globalBody779_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "ry", Flapjack.Exp.var Flapjack.VarKind.local "ry",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp4"]

def globalBody779_40 : Prog (BitVec 64) :=
.seq globalBody779_38 globalBody779_39

def globalBody779_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp2", Flapjack.Exp.var Flapjack.VarKind.local "tmp2",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp2"]

def globalBody779_42 : Prog (BitVec 64) :=
.seq globalBody779_40 globalBody779_41

def globalBody779_43 : Prog (BitVec 64) :=
.seq globalBody779_42 globalBody779_41

def globalBody779_44 : Prog (BitVec 64) :=
.seq globalBody779_43 globalBody779_41

def globalBody779_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "ry", Flapjack.Exp.var Flapjack.VarKind.local "ry",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp2"]

def globalBody779_46 : Prog (BitVec 64) :=
.seq globalBody779_44 globalBody779_45

def globalBody779_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "rx", Flapjack.Exp.var Flapjack.VarKind.local "nx"]

def globalBody779_48 : Prog (BitVec 64) :=
.seq globalBody779_46 globalBody779_47

def globalBody779_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp3", Flapjack.Exp.var Flapjack.VarKind.local "tmp4",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def globalBody779_50 : Prog (BitVec 64) :=
.seq globalBody779_48 globalBody779_49

def globalBody779_51 : Prog (BitVec 64) :=
.seq globalBody779_50 globalBody779_13

def globalBody779_52 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_neg"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "tmp3"]

def globalBody779_53 : Prog (BitVec 64) :=
.seq globalBody779_51 globalBody779_52

def globalBody779_54 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp6"]

def globalBody779_55 : Prog (BitVec 64) :=
.seq globalBody779_53 globalBody779_54

def globalBody779_56 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp6",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def globalBody779_57 : Prog (BitVec 64) :=
.seq globalBody779_55 globalBody779_56

def globalBody779_58 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp6",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp5"]

def globalBody779_59 : Prog (BitVec 64) :=
.seq globalBody779_57 globalBody779_58

def globalBody779_60 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp1", Flapjack.Exp.var Flapjack.VarKind.local "tmp1",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def globalBody779_61 : Prog (BitVec 64) :=
.seq globalBody779_59 globalBody779_60

def globalBody779_62 : Prog (BitVec 64) :=
.seq globalBody779_61 globalBody779_60

def globalBody779_63 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sub"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "tmp6", Flapjack.Exp.var Flapjack.VarKind.local "tmp1"]

def globalBody779_64 : Prog (BitVec 64) :=
.seq globalBody779_62 globalBody779_63

def globalBody779_65 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "tmp0", Flapjack.Exp.var Flapjack.VarKind.local "rz",
    Flapjack.Exp.var Flapjack.VarKind.local "zsq"]

def globalBody779_66 : Prog (BitVec 64) :=
.seq globalBody779_64 globalBody779_65

def globalBody779_67 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "co", Flapjack.Exp.var Flapjack.VarKind.local "tmp0",
    Flapjack.Exp.var Flapjack.VarKind.local "tmp0"]

def globalBody779_68 : Prog (BitVec 64) :=
.seq globalBody779_66 globalBody779_67

def globalBody779_69 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody779_70 : Prog (BitVec 64) :=
.seq globalBody779_68 globalBody779_69

def globalBody779_71 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody779_72 : Prog (BitVec 64) :=
.seq globalBody779_70 globalBody779_71

def globalBody779_73 : Prog (BitVec 64) :=
.dec ("rz") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 192#64]) globalBody779_72

def globalBody779_74 : Prog (BitVec 64) :=
.dec ("ry") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rp", Flapjack.Exp.const 96#64]) globalBody779_73

def globalBody779_75 : Prog (BitVec 64) :=
.dec ("rx") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "rp") globalBody779_74

def globalBody779_76 : Prog (BitVec 64) :=
.dec ("nx") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 768#64]) globalBody779_75

def globalBody779_77 : Prog (BitVec 64) :=
.dec ("zsq") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 672#64]) globalBody779_76

def globalBody779_78 : Prog (BitVec 64) :=
.dec ("tmp6") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) globalBody779_77

def globalBody779_79 : Prog (BitVec 64) :=
.dec ("tmp5") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 480#64]) globalBody779_78

def globalBody779_80 : Prog (BitVec 64) :=
.dec ("tmp4") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 384#64]) globalBody779_79

def globalBody779_81 : Prog (BitVec 64) :=
.dec ("tmp3") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) globalBody779_80

def globalBody779_82 : Prog (BitVec 64) :=
.dec ("tmp2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 192#64]) globalBody779_81

def globalBody779_83 : Prog (BitVec 64) :=
.dec ("tmp1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 96#64]) globalBody779_82

def globalBody779_84 : Prog (BitVec 64) :=
.dec ("tmp0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") globalBody779_83

def globalBody779_85 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 9#64]]) globalBody779_84

def globalBody779_86 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody779_85

def globalData779 : Decl (BitVec 64) :=
.function { name := "pair_doubling_step", inline := false, exported := false, params := [("rp", Flapjack.Shape.one), ("co", Flapjack.Shape.one)], body := globalBody779_86, returnShape := (Flapjack.Shape.one) }
def globalOutput779 := Pancake.PanLang.declToHOL globalData779
end InitECandidate.Proofs.FrontendStages.Declarations
