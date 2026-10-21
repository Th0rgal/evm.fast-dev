import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data673
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate657
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody673_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn"]

def globalBody673_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_set_zero"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md"]

def globalBody673_2 : Prog (BitVec 64) :=
.seq globalBody673_0 globalBody673_1

def globalBody673_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn",
    Flapjack.Exp.var Flapjack.VarKind.local "y2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody673_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def globalBody673_5 : Prog (BitVec 64) :=
.seq globalBody673_3 globalBody673_4

def globalBody673_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn",
    Flapjack.Exp.var Flapjack.VarKind.local "mn", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody673_7 : Prog (BitVec 64) :=
.seq globalBody673_5 globalBody673_6

def globalBody673_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "x2", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody673_9 : Prog (BitVec 64) :=
.seq globalBody673_7 globalBody673_8

def globalBody673_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "z2"]

def globalBody673_11 : Prog (BitVec 64) :=
.seq globalBody673_9 globalBody673_10

def globalBody673_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody673_13 : Prog (BitVec 64) :=
.seq globalBody673_11 globalBody673_12

def globalBody673_14 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "P1")
  (Flapjack.Exp.var Flapjack.VarKind.local "P2")) globalBody673_2 globalBody673_13

def globalBody673_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "x1"]

def globalBody673_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn",
    Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.const 3#64]

def globalBody673_17 : Prog (BitVec 64) :=
.seq globalBody673_15 globalBody673_16

def globalBody673_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody673_19 : Prog (BitVec 64) :=
.seq globalBody673_17 globalBody673_18

def globalBody673_20 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.const 2#64]

def globalBody673_21 : Prog (BitVec 64) :=
.seq globalBody673_19 globalBody673_20

def globalBody673_22 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "xt", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody673_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def globalBody673_24 : Prog (BitVec 64) :=
.seq globalBody673_22 globalBody673_23

def globalBody673_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "num", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody673_26 : Prog (BitVec 64) :=
.seq globalBody673_24 globalBody673_25

def globalBody673_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.var Flapjack.VarKind.local "z1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def globalBody673_28 : Prog (BitVec 64) :=
.seq globalBody673_26 globalBody673_27

def globalBody673_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody673_30 : Prog (BitVec 64) :=
.seq globalBody673_28 globalBody673_29

def globalBody673_31 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody673_32 : Prog (BitVec 64) :=
.seq globalBody673_30 globalBody673_31

def globalBody673_33 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mnz") (Flapjack.Exp.const 1#64)) globalBody673_21 globalBody673_32

def globalBody673_34 : Prog (BitVec 64) :=
.decCall ("mnz") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "mn"]) globalBody673_33

def globalBody673_35 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody673_36 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "mdz") (Flapjack.Exp.const 1#64)) globalBody673_34 globalBody673_35

def globalBody673_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "xt", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody673_38 : Prog (BitVec 64) :=
.seq globalBody673_36 globalBody673_37

def globalBody673_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "x1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def globalBody673_40 : Prog (BitVec 64) :=
.seq globalBody673_38 globalBody673_39

def globalBody673_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def globalBody673_42 : Prog (BitVec 64) :=
.seq globalBody673_40 globalBody673_41

def globalBody673_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.var Flapjack.VarKind.local "mn", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody673_44 : Prog (BitVec 64) :=
.seq globalBody673_42 globalBody673_43

def globalBody673_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "yt", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody673_46 : Prog (BitVec 64) :=
.seq globalBody673_44 globalBody673_45

def globalBody673_47 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "y1", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def globalBody673_48 : Prog (BitVec 64) :=
.seq globalBody673_46 globalBody673_47

def globalBody673_49 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "num"]

def globalBody673_50 : Prog (BitVec 64) :=
.seq globalBody673_48 globalBody673_49

def globalBody673_51 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def globalBody673_52 : Prog (BitVec 64) :=
.seq globalBody673_50 globalBody673_51

def globalBody673_53 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "num",
    Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t2"]

def globalBody673_54 : Prog (BitVec 64) :=
.seq globalBody673_52 globalBody673_53

def globalBody673_55 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.var Flapjack.VarKind.local "md", Flapjack.Exp.var Flapjack.VarKind.local "zt"]

def globalBody673_56 : Prog (BitVec 64) :=
.seq globalBody673_54 globalBody673_55

def globalBody673_57 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "den",
    Flapjack.Exp.var Flapjack.VarKind.local "den", Flapjack.Exp.var Flapjack.VarKind.local "z1"]

def globalBody673_58 : Prog (BitVec 64) :=
.seq globalBody673_56 globalBody673_57

def globalBody673_59 : Prog (BitVec 64) :=
.seq globalBody673_58 globalBody673_29

def globalBody673_60 : Prog (BitVec 64) :=
.seq globalBody673_59 globalBody673_31

def globalBody673_61 : Prog (BitVec 64) :=
.decCall ("mdz") (Flapjack.Shape.one) ("fe_is_zero") ([Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "md"]) globalBody673_60

def globalBody673_62 : Prog (BitVec 64) :=
.seq globalBody673_14 globalBody673_61

def globalBody673_63 : Prog (BitVec 64) :=
.decCall ("t2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody673_62

def globalBody673_64 : Prog (BitVec 64) :=
.decCall ("t1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody673_63

def globalBody673_65 : Prog (BitVec 64) :=
.decCall ("md") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody673_64

def globalBody673_66 : Prog (BitVec 64) :=
.decCall ("mn") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody673_65

def globalBody673_67 : Prog (BitVec 64) :=
.dec ("zt") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "T",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody673_66

def globalBody673_68 : Prog (BitVec 64) :=
.dec ("yt") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "T", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody673_67

def globalBody673_69 : Prog (BitVec 64) :=
.dec ("xt") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "T") globalBody673_68

def globalBody673_70 : Prog (BitVec 64) :=
.dec ("z2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P2",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody673_69

def globalBody673_71 : Prog (BitVec 64) :=
.dec ("y2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P2", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody673_70

def globalBody673_72 : Prog (BitVec 64) :=
.dec ("x2") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "P2") globalBody673_71

def globalBody673_73 : Prog (BitVec 64) :=
.dec ("z1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P1",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody673_72

def globalBody673_74 : Prog (BitVec 64) :=
.dec ("y1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "P1", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody673_73

def globalBody673_75 : Prog (BitVec 64) :=
.dec ("x1") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "P1") globalBody673_74

def globalBody673_76 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody673_75

def globalBody673_77 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) globalBody673_76

def globalData673 : Decl (BitVec 64) :=
.function { name := "ecp_linefunc", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("num", Flapjack.Shape.one), ("den", Flapjack.Shape.one), ("P1", Flapjack.Shape.one),
  ("P2", Flapjack.Shape.one), ("T", Flapjack.Shape.one)], body := globalBody673_77, returnShape := (Flapjack.Shape.one) }
def globalOutput673 := Pancake.PanLang.declToHOL globalData673
end InitECandidate.Proofs.FrontendStages.Declarations
