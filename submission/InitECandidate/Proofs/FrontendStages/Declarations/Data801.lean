import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify785
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body801_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "g2_decode"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 256#64],
    Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def body801_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body801_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 1#64)) body801_0 body801_1

def body801_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body801_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body801_5 : Prog (BitVec 64) :=
.seq body801_3 body801_4

def body801_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body801_5 body801_1

def body801_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def body801_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body801_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body801_10 : Prog (BitVec 64) :=
.seq body801_3 body801_9

def body801_11 : Prog (BitVec 64) :=
.seq body801_8 body801_10

def body801_12 : Prog (BitVec 64) :=
.seq body801_7 body801_11

def body801_13 : Prog (BitVec 64) :=
.seq body801_6 body801_12

def body801_14 : Prog (BitVec 64) :=
.seq body801_2 body801_13

def body801_15 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g2_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body801_14

def body801_16 : Prog (BitVec 64) :=
.decCall ("p2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body801_15

def body801_17 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body801_16

def body801_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body801_17

def body801_19 : Prog (BitVec 64) :=
.seq body801_2 body801_6

def body801_20 : Prog (BitVec 64) :=
.seq body801_19 body801_7

def body801_21 : Prog (BitVec 64) :=
.seq body801_20 body801_8

def body801_22 : Prog (BitVec 64) :=
.seq body801_21 body801_3

def body801_23 : Prog (BitVec 64) :=
.seq body801_22 body801_9

def body801_24 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g2_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body801_23

def body801_25 : Prog (BitVec 64) :=
.decCall ("p2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body801_24

def body801_26 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 288#64]) body801_25

def body801_27 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body801_26

def originalData801 : Decl (BitVec 64) :=
.function { name := "bls_g2_add_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body801_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData801 : Decl (BitVec 64) :=
.function { name := "bls_g2_add_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body801_27, returnShape := (Flapjack.Shape.one) }
def original801 := Pancake.PanLang.declToHOL originalData801
def simplified801 := Pancake.PanLang.declToHOL simplifiedData801
end InitECandidate.Proofs.FrontendStages.Declarations
