import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data754
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate738
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody754_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "f"]

def globalBody754_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.local "f"]

def globalBody754_2 : Prog (BitVec 64) :=
.seq globalBody754_0 globalBody754_1

def globalBody754_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "m", Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody754_4 : Prog (BitVec 64) :=
.seq globalBody754_2 globalBody754_3

def globalBody754_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m"]

def globalBody754_6 : Prog (BitVec 64) :=
.seq globalBody754_4 globalBody754_5

def globalBody754_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody754_8 : Prog (BitVec 64) :=
.seq globalBody754_6 globalBody754_7

def globalBody754_9 : Prog (BitVec 64) :=
.seq globalBody754_8 globalBody754_3

def globalBody754_10 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "m"]

def globalBody754_11 : Prog (BitVec 64) :=
.seq globalBody754_9 globalBody754_10

def globalBody754_12 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m"]

def globalBody754_13 : Prog (BitVec 64) :=
.seq globalBody754_11 globalBody754_12

def globalBody754_14 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody754_15 : Prog (BitVec 64) :=
.seq globalBody754_13 globalBody754_14

def globalBody754_16 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody754_17 : Prog (BitVec 64) :=
.seq globalBody754_15 globalBody754_16

def globalBody754_18 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody754_19 : Prog (BitVec 64) :=
.seq globalBody754_17 globalBody754_18

def globalBody754_20 : Prog (BitVec 64) :=
.seq globalBody754_19 globalBody754_14

def globalBody754_21 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody754_22 : Prog (BitVec 64) :=
.seq globalBody754_20 globalBody754_21

def globalBody754_23 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody754_24 : Prog (BitVec 64) :=
.seq globalBody754_22 globalBody754_23

def globalBody754_25 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "b",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody754_26 : Prog (BitVec 64) :=
.seq globalBody754_24 globalBody754_25

def globalBody754_27 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "b"]

def globalBody754_28 : Prog (BitVec 64) :=
.seq globalBody754_26 globalBody754_27

def globalBody754_29 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_exp_x"
  [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "c"]

def globalBody754_30 : Prog (BitVec 64) :=
.seq globalBody754_28 globalBody754_29

def globalBody754_31 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_frob"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "b"]

def globalBody754_32 : Prog (BitVec 64) :=
.seq globalBody754_30 globalBody754_31

def globalBody754_33 : Prog (BitVec 64) :=
.seq globalBody754_32 globalBody754_7

def globalBody754_34 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "c", Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody754_35 : Prog (BitVec 64) :=
.seq globalBody754_33 globalBody754_34

def globalBody754_36 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_conj"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "b"]

def globalBody754_37 : Prog (BitVec 64) :=
.seq globalBody754_35 globalBody754_36

def globalBody754_38 : Prog (BitVec 64) :=
.seq globalBody754_37 globalBody754_34

def globalBody754_39 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "m",
    Flapjack.Exp.var Flapjack.VarKind.local "m"]

def globalBody754_40 : Prog (BitVec 64) :=
.seq globalBody754_38 globalBody754_39

def globalBody754_41 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "u", Flapjack.Exp.var Flapjack.VarKind.local "u",
    Flapjack.Exp.var Flapjack.VarKind.local "m"]

def globalBody754_42 : Prog (BitVec 64) :=
.seq globalBody754_40 globalBody754_41

def globalBody754_43 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp12_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "c",
    Flapjack.Exp.var Flapjack.VarKind.local "u"]

def globalBody754_44 : Prog (BitVec 64) :=
.seq globalBody754_42 globalBody754_43

def globalBody754_45 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody754_46 : Prog (BitVec 64) :=
.seq globalBody754_44 globalBody754_45

def globalBody754_47 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody754_48 : Prog (BitVec 64) :=
.seq globalBody754_46 globalBody754_47

def globalBody754_49 : Prog (BitVec 64) :=
.dec ("u") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 2304#64]) globalBody754_48

def globalBody754_50 : Prog (BitVec 64) :=
.dec ("c") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1728#64]) globalBody754_49

def globalBody754_51 : Prog (BitVec 64) :=
.dec ("b") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1152#64]) globalBody754_50

def globalBody754_52 : Prog (BitVec 64) :=
.dec ("a") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) globalBody754_51

def globalBody754_53 : Prog (BitVec 64) :=
.dec ("m") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") globalBody754_52

def globalBody754_54 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 576#64, Flapjack.Exp.const 5#64]]) globalBody754_53

def globalBody754_55 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody754_54

def globalData754 : Decl (BitVec 64) :=
.function { name := "fp12_final_exp", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("f", Flapjack.Shape.one)], body := globalBody754_55, returnShape := (Flapjack.Shape.one) }
def globalOutput754 := Pancake.PanLang.declToHOL globalData754
end InitECandidate.Proofs.FrontendStages.Declarations
