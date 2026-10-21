import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify670
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body686_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body686_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def body686_2 : Prog (BitVec 64) :=
.seq body686_0 body686_1

def body686_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body686_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e0") (Flapjack.Exp.const 0#64)) body686_2 body686_3

def body686_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "e1") (Flapjack.Exp.const 0#64)) body686_2 body686_3

def body686_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "ecp_add"
  [Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "p0", Flapjack.Exp.var Flapjack.VarKind.local "p0",
    Flapjack.Exp.var Flapjack.VarKind.local "p1"]

def body686_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bn254_g1_to_bytes"
  [Flapjack.Exp.var Flapjack.VarKind.local "p0", Flapjack.Exp.var Flapjack.VarKind.local "out64"]

def body686_8 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body686_9 : Prog (BitVec 64) :=
.seq body686_0 body686_8

def body686_10 : Prog (BitVec 64) :=
.seq body686_7 body686_9

def body686_11 : Prog (BitVec 64) :=
.seq body686_6 body686_10

def body686_12 : Prog (BitVec 64) :=
.seq body686_5 body686_11

def body686_13 : Prog (BitVec 64) :=
.decCall ("e1") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "in128", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body686_12

def body686_14 : Prog (BitVec 64) :=
.seq body686_4 body686_13

def body686_15 : Prog (BitVec 64) :=
.decCall ("e0") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "in128", Flapjack.Exp.var Flapjack.VarKind.local "p0"]) body686_14

def body686_16 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body686_15

def body686_17 : Prog (BitVec 64) :=
.decCall ("p0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body686_16

def body686_18 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body686_17

def body686_19 : Prog (BitVec 64) :=
.seq body686_5 body686_6

def body686_20 : Prog (BitVec 64) :=
.seq body686_19 body686_7

def body686_21 : Prog (BitVec 64) :=
.seq body686_20 body686_0

def body686_22 : Prog (BitVec 64) :=
.seq body686_21 body686_8

def body686_23 : Prog (BitVec 64) :=
.decCall ("e1") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "in128", Flapjack.Exp.const 64#64],
  Flapjack.Exp.var Flapjack.VarKind.local "p1"]) body686_22

def body686_24 : Prog (BitVec 64) :=
.seq body686_4 body686_23

def body686_25 : Prog (BitVec 64) :=
.decCall ("e0") (Flapjack.Shape.one) ("bn254_parse_g1") ([Flapjack.Exp.var Flapjack.VarKind.local "in128", Flapjack.Exp.var Flapjack.VarKind.local "p0"]) body686_24

def body686_26 : Prog (BitVec 64) :=
.decCall ("p1") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body686_25

def body686_27 : Prog (BitVec 64) :=
.decCall ("p0") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body686_26

def body686_28 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body686_27

def originalData686 : Decl (BitVec 64) :=
.function { name := "bn254_g1_add", inline := false, exported := false, params := [("in128", Flapjack.Shape.one), ("out64", Flapjack.Shape.one)], body := body686_18, returnShape := (Flapjack.Shape.one) }
def simplifiedData686 : Decl (BitVec 64) :=
.function { name := "bn254_g1_add", inline := false, exported := false, params := [("in128", Flapjack.Shape.one), ("out64", Flapjack.Shape.one)], body := body686_28, returnShape := (Flapjack.Shape.one) }
def original686 := Pancake.PanLang.declToHOL originalData686
def simplified686 := Pancake.PanLang.declToHOL simplifiedData686
end InitECandidate.Proofs.FrontendStages.Declarations
