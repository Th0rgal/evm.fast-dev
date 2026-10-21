import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify771
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body787_0 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "zp") (Flapjack.Exp.var Flapjack.VarKind.local "zk")

def body787_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "zk"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "zk", Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body787_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "zp",
      Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 48#64]])
  (Flapjack.Exp.var Flapjack.VarKind.local "zk")

def body787_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "j"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "j", Flapjack.Exp.const 1#64])

def body787_4 : Prog (BitVec 64) :=
.seq body787_2 body787_3

def body787_5 : Prog (BitVec 64) :=
.seq body787_1 body787_4

def body787_6 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 15#64)) body787_5

def body787_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "m1"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body787_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "m2"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "m2", Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body787_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "m3"), none)) "bls_fp_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "m3", Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body787_10 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.var Flapjack.VarKind.local "r") (Flapjack.Exp.var Flapjack.VarKind.local "rx")

def body787_11 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 48#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "ry")

def body787_12 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rz")

def body787_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body787_14 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body787_15 : Prog (BitVec 64) :=
.seq body787_13 body787_14

def body787_16 : Prog (BitVec 64) :=
.seq body787_12 body787_15

def body787_17 : Prog (BitVec 64) :=
.seq body787_11 body787_16

def body787_18 : Prog (BitVec 64) :=
.seq body787_10 body787_17

def body787_19 : Prog (BitVec 64) :=
.decCall ("rz") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.var Flapjack.VarKind.local "m3"]) body787_18

def body787_20 : Prog (BitVec 64) :=
.decCall ("ry") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.var Flapjack.VarKind.local "m2"]) body787_19

def body787_21 : Prog (BitVec 64) :=
.decCall ("rx") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.var Flapjack.VarKind.local "m3"]) body787_20

def body787_22 : Prog (BitVec 64) :=
.seq body787_9 body787_21

def body787_23 : Prog (BitVec 64) :=
.seq body787_8 body787_22

def body787_24 : Prog (BitVec 64) :=
.seq body787_7 body787_23

def body787_25 : Prog (BitVec 64) :=
.decCall ("m3") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 3776#64],
  Flapjack.Exp.const 16#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_24

def body787_26 : Prog (BitVec 64) :=
.decCall ("m2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 3008#64],
  Flapjack.Exp.const 16#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_25

def body787_27 : Prog (BitVec 64) :=
.decCall ("m1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 2480#64],
  Flapjack.Exp.const 11#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_26

def body787_28 : Prog (BitVec 64) :=
.decCall ("m0") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1904#64],
  Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_27

def body787_29 : Prog (BitVec 64) :=
.seq body787_6 body787_28

def body787_30 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body787_29

def body787_31 : Prog (BitVec 64) :=
.seq body787_0 body787_30

def body787_32 : Prog (BitVec 64) :=
.dec ("zk") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "z") body787_31

def body787_33 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64])) body787_32

def body787_34 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 48#64])) body787_33

def body787_35 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")) body787_34

def body787_36 : Prog (BitVec 64) :=
.decCall ("zp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 48#64, Flapjack.Exp.const 15#64]]) body787_35

def body787_37 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body787_36

def body787_38 : Prog (BitVec 64) :=
.seq body787_1 body787_2

def body787_39 : Prog (BitVec 64) :=
.seq body787_38 body787_3

def body787_40 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "j") (Flapjack.Exp.const 15#64)) body787_39

def body787_41 : Prog (BitVec 64) :=
.seq body787_7 body787_8

def body787_42 : Prog (BitVec 64) :=
.seq body787_41 body787_9

def body787_43 : Prog (BitVec 64) :=
.seq body787_10 body787_11

def body787_44 : Prog (BitVec 64) :=
.seq body787_43 body787_12

def body787_45 : Prog (BitVec 64) :=
.seq body787_44 body787_13

def body787_46 : Prog (BitVec 64) :=
.seq body787_45 body787_14

def body787_47 : Prog (BitVec 64) :=
.decCall ("rz") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.var Flapjack.VarKind.local "m3"]) body787_46

def body787_48 : Prog (BitVec 64) :=
.decCall ("ry") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "m1", Flapjack.Exp.var Flapjack.VarKind.local "m2"]) body787_47

def body787_49 : Prog (BitVec 64) :=
.decCall ("rx") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("bls_fp_mul") ([Flapjack.Exp.var Flapjack.VarKind.local "m0", Flapjack.Exp.var Flapjack.VarKind.local "m3"]) body787_48

def body787_50 : Prog (BitVec 64) :=
.seq body787_42 body787_49

def body787_51 : Prog (BitVec 64) :=
.decCall ("m3") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 3776#64],
  Flapjack.Exp.const 16#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_50

def body787_52 : Prog (BitVec 64) :=
.decCall ("m2") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 3008#64],
  Flapjack.Exp.const 16#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_51

def body787_53 : Prog (BitVec 64) :=
.decCall ("m1") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 2480#64],
  Flapjack.Exp.const 11#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_52

def body787_54 : Prog (BitVec 64) :=
.decCall ("m0") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) ("iso_horner_fp") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 1904#64],
  Flapjack.Exp.const 12#64, Flapjack.Exp.var Flapjack.VarKind.local "x", Flapjack.Exp.var Flapjack.VarKind.local "zp"]) body787_53

def body787_55 : Prog (BitVec 64) :=
.seq body787_40 body787_54

def body787_56 : Prog (BitVec 64) :=
.dec ("j") (Flapjack.Shape.one) (Flapjack.Exp.const 1#64) body787_55

def body787_57 : Prog (BitVec 64) :=
.seq body787_0 body787_56

def body787_58 : Prog (BitVec 64) :=
.dec ("zk") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.var Flapjack.VarKind.local "z") body787_57

def body787_59 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64])) body787_58

def body787_60 : Prog (BitVec 64) :=
.dec ("y") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 48#64])) body787_59

def body787_61 : Prog (BitVec 64) :=
.dec ("x") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.var Flapjack.VarKind.local "p")) body787_60

def body787_62 : Prog (BitVec 64) :=
.decCall ("zp") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 48#64, Flapjack.Exp.const 15#64]]) body787_61

def body787_63 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body787_62

def originalData787 : Decl (BitVec 64) :=
.function { name := "iso_map_g1", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body787_37, returnShape := (Flapjack.Shape.one) }
def simplifiedData787 : Decl (BitVec 64) :=
.function { name := "iso_map_g1", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("p", Flapjack.Shape.one)], body := body787_63, returnShape := (Flapjack.Shape.one) }
def original787 := Pancake.PanLang.declToHOL originalData787
def simplified787 := Pancake.PanLang.declToHOL simplifiedData787
end InitECandidate.Proofs.FrontendStages.Declarations
