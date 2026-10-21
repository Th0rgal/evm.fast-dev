import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify759
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body775_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.var Flapjack.VarKind.local "y"]

def body775_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "rr", Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body775_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "rr", Flapjack.Exp.var Flapjack.VarKind.local "rr",
    Flapjack.Exp.var Flapjack.VarKind.local "x"]

def body775_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "rr", Flapjack.Exp.var Flapjack.VarKind.local "rr",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "bls_c", Flapjack.Exp.const 288#64]]

def body775_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body775_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "e")

def body775_6 : Prog (BitVec 64) :=
.seq body775_4 body775_5

def body775_7 : Prog (BitVec 64) :=
.decCall ("e") (Flapjack.Shape.one) ("fp2_eq") ([Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.var Flapjack.VarKind.local "rr"]) body775_6

def body775_8 : Prog (BitVec 64) :=
.seq body775_3 body775_7

def body775_9 : Prog (BitVec 64) :=
.seq body775_2 body775_8

def body775_10 : Prog (BitVec 64) :=
.seq body775_1 body775_9

def body775_11 : Prog (BitVec 64) :=
.seq body775_0 body775_10

def body775_12 : Prog (BitVec 64) :=
.decCall ("rr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body775_11

def body775_13 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body775_12

def body775_14 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body775_13

def body775_15 : Prog (BitVec 64) :=
.seq body775_0 body775_1

def body775_16 : Prog (BitVec 64) :=
.seq body775_15 body775_2

def body775_17 : Prog (BitVec 64) :=
.seq body775_16 body775_3

def body775_18 : Prog (BitVec 64) :=
.seq body775_17 body775_7

def body775_19 : Prog (BitVec 64) :=
.decCall ("rr") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body775_18

def body775_20 : Prog (BitVec 64) :=
.decCall ("l") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body775_19

def body775_21 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body775_20

def originalData775 : Decl (BitVec 64) :=
.function { name := "g2_on_curve", inline := false, exported := false, params := [("x", Flapjack.Shape.one), ("y", Flapjack.Shape.one)], body := body775_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData775 : Decl (BitVec 64) :=
.function { name := "g2_on_curve", inline := false, exported := false, params := [("x", Flapjack.Shape.one), ("y", Flapjack.Shape.one)], body := body775_21, returnShape := (Flapjack.Shape.one) }
def original775 := Pancake.PanLang.declToHOL originalData775
def simplified775 := Pancake.PanLang.declToHOL simplifiedData775
end InitECandidate.Proofs.FrontendStages.Declarations
