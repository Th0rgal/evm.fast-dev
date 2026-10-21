import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify783
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body799_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (some (Flapjack.VarKind.local, "ok"), none)) "g1_decode"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.const 128#64],
    Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def body799_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body799_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 1#64)) body799_0 body799_1

def body799_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body799_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body799_5 : Prog (BitVec 64) :=
.seq body799_3 body799_4

def body799_6 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "ok") (Flapjack.Exp.const 0#64)) body799_5 body799_1

def body799_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "p1",
    Flapjack.Exp.var Flapjack.VarKind.local "p2"]

def body799_8 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_encode"
  [Flapjack.Exp.var Flapjack.VarKind.local "p1", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body799_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body799_10 : Prog (BitVec 64) :=
.seq body799_3 body799_9

def body799_11 : Prog (BitVec 64) :=
.seq body799_8 body799_10

def body799_12 : Prog (BitVec 64) :=
.seq body799_7 body799_11

def body799_13 : Prog (BitVec 64) :=
.seq body799_6 body799_12

def body799_14 : Prog (BitVec 64) :=
.seq body799_2 body799_13

def body799_15 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g1_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body799_14

def body799_16 : Prog (BitVec 64) :=
.decCall ("p2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body799_15

def body799_17 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body799_16

def body799_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body799_17

def body799_19 : Prog (BitVec 64) :=
.seq body799_2 body799_6

def body799_20 : Prog (BitVec 64) :=
.seq body799_19 body799_7

def body799_21 : Prog (BitVec 64) :=
.seq body799_20 body799_8

def body799_22 : Prog (BitVec 64) :=
.seq body799_21 body799_3

def body799_23 : Prog (BitVec 64) :=
.seq body799_22 body799_9

def body799_24 : Prog (BitVec 64) :=
.decCall ("ok") (Flapjack.Shape.one) ("g1_decode") ([Flapjack.Exp.var Flapjack.VarKind.local "data", Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body799_23

def body799_25 : Prog (BitVec 64) :=
.decCall ("p2") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body799_24

def body799_26 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 144#64]) body799_25

def body799_27 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body799_26

def originalData799 : Decl (BitVec 64) :=
.function { name := "bls_g1_add_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body799_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData799 : Decl (BitVec 64) :=
.function { name := "bls_g1_add_exec", inline := false, exported := false, params := [("data", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body799_27, returnShape := (Flapjack.Shape.one) }
def original799 := Pancake.PanLang.declToHOL originalData799
def simplified799 := Pancake.PanLang.declToHOL simplifiedData799
end InitECandidate.Proofs.FrontendStages.Declarations
