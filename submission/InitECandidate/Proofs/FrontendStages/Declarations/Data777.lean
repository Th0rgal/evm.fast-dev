import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify761
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body777_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g2_normalize"
  [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body777_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body777_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.const 48#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64]]

def body777_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.const 96#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 128#64]]

def body777_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.const 144#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 192#64]]

def body777_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body777_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body777_7 : Prog (BitVec 64) :=
.seq body777_5 body777_6

def body777_8 : Prog (BitVec 64) :=
.seq body777_4 body777_7

def body777_9 : Prog (BitVec 64) :=
.seq body777_3 body777_8

def body777_10 : Prog (BitVec 64) :=
.seq body777_2 body777_9

def body777_11 : Prog (BitVec 64) :=
.seq body777_1 body777_10

def body777_12 : Prog (BitVec 64) :=
.seq body777_0 body777_11

def body777_13 : Prog (BitVec 64) :=
.decCall ("aff") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) body777_12

def body777_14 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body777_13

def body777_15 : Prog (BitVec 64) :=
.seq body777_0 body777_1

def body777_16 : Prog (BitVec 64) :=
.seq body777_15 body777_2

def body777_17 : Prog (BitVec 64) :=
.seq body777_16 body777_3

def body777_18 : Prog (BitVec 64) :=
.seq body777_17 body777_4

def body777_19 : Prog (BitVec 64) :=
.seq body777_18 body777_5

def body777_20 : Prog (BitVec 64) :=
.seq body777_19 body777_6

def body777_21 : Prog (BitVec 64) :=
.decCall ("aff") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 192#64]) body777_20

def body777_22 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body777_21

def originalData777 : Decl (BitVec 64) :=
.function { name := "g2_encode", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body777_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData777 : Decl (BitVec 64) :=
.function { name := "g2_encode", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body777_22, returnShape := (Flapjack.Shape.one) }
def original777 := Pancake.PanLang.declToHOL originalData777
def simplified777 := Pancake.PanLang.declToHOL simplifiedData777
end InitECandidate.Proofs.FrontendStages.Declarations
