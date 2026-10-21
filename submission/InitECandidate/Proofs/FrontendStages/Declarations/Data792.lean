import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify776
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body792_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body792_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body792_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body792_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 5600#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def body792_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 5984#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def body792_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 6368#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def body792_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "iso_horner_fp2"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 6752#64],
    Flapjack.Exp.const 4#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def body792_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64],
    Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body792_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64],
    Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body792_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64]]

def body792_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 192#64]]

def body792_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zp", Flapjack.Exp.const 192#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.const 288#64]]

def body792_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_copy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "zp"]

def body792_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body792_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body792_15 : Prog (BitVec 64) :=
.seq body792_13 body792_14

def body792_16 : Prog (BitVec 64) :=
.seq body792_12 body792_15

def body792_17 : Prog (BitVec 64) :=
.seq body792_11 body792_16

def body792_18 : Prog (BitVec 64) :=
.seq body792_10 body792_17

def body792_19 : Prog (BitVec 64) :=
.seq body792_9 body792_18

def body792_20 : Prog (BitVec 64) :=
.seq body792_8 body792_19

def body792_21 : Prog (BitVec 64) :=
.seq body792_7 body792_20

def body792_22 : Prog (BitVec 64) :=
.seq body792_6 body792_21

def body792_23 : Prog (BitVec 64) :=
.seq body792_5 body792_22

def body792_24 : Prog (BitVec 64) :=
.seq body792_4 body792_23

def body792_25 : Prog (BitVec 64) :=
.seq body792_3 body792_24

def body792_26 : Prog (BitVec 64) :=
.seq body792_2 body792_25

def body792_27 : Prog (BitVec 64) :=
.seq body792_1 body792_26

def body792_28 : Prog (BitVec 64) :=
.seq body792_0 body792_27

def body792_29 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]) body792_28

def body792_30 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64]) body792_29

def body792_31 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body792_30

def body792_32 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 4#64]]) body792_31

def body792_33 : Prog (BitVec 64) :=
.decCall ("zp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 3#64]]) body792_32

def body792_34 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body792_33

def body792_35 : Prog (BitVec 64) :=
.seq body792_0 body792_1

def body792_36 : Prog (BitVec 64) :=
.seq body792_35 body792_2

def body792_37 : Prog (BitVec 64) :=
.seq body792_36 body792_3

def body792_38 : Prog (BitVec 64) :=
.seq body792_37 body792_4

def body792_39 : Prog (BitVec 64) :=
.seq body792_38 body792_5

def body792_40 : Prog (BitVec 64) :=
.seq body792_39 body792_6

def body792_41 : Prog (BitVec 64) :=
.seq body792_40 body792_7

def body792_42 : Prog (BitVec 64) :=
.seq body792_41 body792_8

def body792_43 : Prog (BitVec 64) :=
.seq body792_42 body792_9

def body792_44 : Prog (BitVec 64) :=
.seq body792_43 body792_10

def body792_45 : Prog (BitVec 64) :=
.seq body792_44 body792_11

def body792_46 : Prog (BitVec 64) :=
.seq body792_45 body792_12

def body792_47 : Prog (BitVec 64) :=
.seq body792_46 body792_13

def body792_48 : Prog (BitVec 64) :=
.seq body792_47 body792_14

def body792_49 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]) body792_48

def body792_50 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64]) body792_49

def body792_51 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "p") body792_50

def body792_52 : Prog (BitVec 64) :=
.decCall ("m") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 4#64]]) body792_51

def body792_53 : Prog (BitVec 64) :=
.decCall ("zp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 96#64, Flapjack.Exp.const 3#64]]) body792_52

def body792_54 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body792_53

def originalData792 : Decl (BitVec 64) :=
.function { name := "iso_map_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body792_34, returnShape := (Flapjack.Shape.one) }
def simplifiedData792 : Decl (BitVec 64) :=
.function { name := "iso_map_g2", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body792_54, returnShape := (Flapjack.Shape.one) }
def original792 := Pancake.PanLang.declToHOL originalData792
def simplified792 := Pancake.PanLang.declToHOL simplifiedData792
end InitECandidate.Proofs.FrontendStages.Declarations
