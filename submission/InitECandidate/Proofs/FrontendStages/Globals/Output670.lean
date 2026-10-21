import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data670
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate654
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody670_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T1",
    Flapjack.Exp.var Flapjack.VarKind.local "x"]

def globalBody670_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "T1", Flapjack.Exp.const 3#64]

def globalBody670_2 : Prog (BitVec 64) :=
.seq globalBody670_0 globalBody670_1

def globalBody670_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "S",
    Flapjack.Exp.var Flapjack.VarKind.local "y", Flapjack.Exp.var Flapjack.VarKind.local "z"]

def globalBody670_4 : Prog (BitVec 64) :=
.seq globalBody670_2 globalBody670_3

def globalBody670_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T1",
    Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "y"]

def globalBody670_6 : Prog (BitVec 64) :=
.seq globalBody670_4 globalBody670_5

def globalBody670_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "B",
    Flapjack.Exp.var Flapjack.VarKind.local "T1", Flapjack.Exp.var Flapjack.VarKind.local "S"]

def globalBody670_8 : Prog (BitVec 64) :=
.seq globalBody670_6 globalBody670_7

def globalBody670_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T1",
    Flapjack.Exp.var Flapjack.VarKind.local "W"]

def globalBody670_10 : Prog (BitVec 64) :=
.seq globalBody670_8 globalBody670_9

def globalBody670_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T2",
    Flapjack.Exp.var Flapjack.VarKind.local "B", Flapjack.Exp.const 8#64]

def globalBody670_12 : Prog (BitVec 64) :=
.seq globalBody670_10 globalBody670_11

def globalBody670_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "H",
    Flapjack.Exp.var Flapjack.VarKind.local "T1", Flapjack.Exp.var Flapjack.VarKind.local "T2"]

def globalBody670_14 : Prog (BitVec 64) :=
.seq globalBody670_12 globalBody670_13

def globalBody670_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "S2",
    Flapjack.Exp.var Flapjack.VarKind.local "S"]

def globalBody670_16 : Prog (BitVec 64) :=
.seq globalBody670_14 globalBody670_15

def globalBody670_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T1",
    Flapjack.Exp.var Flapjack.VarKind.local "H", Flapjack.Exp.var Flapjack.VarKind.local "S"]

def globalBody670_18 : Prog (BitVec 64) :=
.seq globalBody670_16 globalBody670_17

def globalBody670_19 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T1",
    Flapjack.Exp.var Flapjack.VarKind.local "T1", Flapjack.Exp.const 2#64]

def globalBody670_20 : Prog (BitVec 64) :=
.seq globalBody670_18 globalBody670_19

def globalBody670_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T2",
    Flapjack.Exp.var Flapjack.VarKind.local "B", Flapjack.Exp.const 4#64]

def globalBody670_22 : Prog (BitVec 64) :=
.seq globalBody670_20 globalBody670_21

def globalBody670_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T2",
    Flapjack.Exp.var Flapjack.VarKind.local "T2", Flapjack.Exp.var Flapjack.VarKind.local "H"]

def globalBody670_24 : Prog (BitVec 64) :=
.seq globalBody670_22 globalBody670_23

def globalBody670_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T2",
    Flapjack.Exp.var Flapjack.VarKind.local "W", Flapjack.Exp.var Flapjack.VarKind.local "T2"]

def globalBody670_26 : Prog (BitVec 64) :=
.seq globalBody670_24 globalBody670_25

def globalBody670_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "y"]

def globalBody670_28 : Prog (BitVec 64) :=
.seq globalBody670_26 globalBody670_27

def globalBody670_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "W", Flapjack.Exp.var Flapjack.VarKind.local "S2"]

def globalBody670_30 : Prog (BitVec 64) :=
.seq globalBody670_28 globalBody670_29

def globalBody670_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "W",
    Flapjack.Exp.var Flapjack.VarKind.local "W", Flapjack.Exp.const 8#64]

def globalBody670_32 : Prog (BitVec 64) :=
.seq globalBody670_30 globalBody670_31

def globalBody670_33 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "T2",
    Flapjack.Exp.var Flapjack.VarKind.local "T2", Flapjack.Exp.var Flapjack.VarKind.local "W"]

def globalBody670_34 : Prog (BitVec 64) :=
.seq globalBody670_32 globalBody670_33

def globalBody670_35 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "S",
    Flapjack.Exp.var Flapjack.VarKind.local "S", Flapjack.Exp.var Flapjack.VarKind.local "S2"]

def globalBody670_36 : Prog (BitVec 64) :=
.seq globalBody670_34 globalBody670_35

def globalBody670_37 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul_small"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "S",
    Flapjack.Exp.var Flapjack.VarKind.local "S", Flapjack.Exp.const 8#64]

def globalBody670_38 : Prog (BitVec 64) :=
.seq globalBody670_36 globalBody670_37

def globalBody670_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "T1",
    Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody670_40 : Prog (BitVec 64) :=
.seq globalBody670_38 globalBody670_39

def globalBody670_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "esz"],
    Flapjack.Exp.var Flapjack.VarKind.local "T2", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody670_42 : Prog (BitVec 64) :=
.seq globalBody670_40 globalBody670_41

def globalBody670_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "out",
        Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]],
    Flapjack.Exp.var Flapjack.VarKind.local "S", Flapjack.Exp.var Flapjack.VarKind.local "esz"]

def globalBody670_44 : Prog (BitVec 64) :=
.seq globalBody670_42 globalBody670_43

def globalBody670_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody670_46 : Prog (BitVec 64) :=
.seq globalBody670_44 globalBody670_45

def globalBody670_47 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody670_48 : Prog (BitVec 64) :=
.seq globalBody670_46 globalBody670_47

def globalBody670_49 : Prog (BitVec 64) :=
.decCall ("T2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_48

def globalBody670_50 : Prog (BitVec 64) :=
.decCall ("T1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_49

def globalBody670_51 : Prog (BitVec 64) :=
.decCall ("S2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_50

def globalBody670_52 : Prog (BitVec 64) :=
.decCall ("H") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_51

def globalBody670_53 : Prog (BitVec 64) :=
.decCall ("B") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_52

def globalBody670_54 : Prog (BitVec 64) :=
.decCall ("S") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_53

def globalBody670_55 : Prog (BitVec 64) :=
.decCall ("W") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_54

def globalBody670_56 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "pt",
    Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "esz"]]) globalBody670_55

def globalBody670_57 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "pt", Flapjack.Exp.var Flapjack.VarKind.local "esz"]) globalBody670_56

def globalBody670_58 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "pt") globalBody670_57

def globalBody670_59 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody670_58

def globalBody670_60 : Prog (BitVec 64) :=
.dec ("esz") (Flapjack.Shape.one) (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.const 32#64]) globalBody670_59

def globalData670 : Decl (BitVec 64) :=
.function { name := "ecp_double", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("out", Flapjack.Shape.one), ("pt", Flapjack.Shape.one)], body := globalBody670_60, returnShape := (Flapjack.Shape.one) }
def globalOutput670 := Pancake.PanLang.declToHOL globalData670
end InitECandidate.Proofs.FrontendStages.Declarations
