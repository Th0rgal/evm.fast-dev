import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify749
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body765_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "g1_normalize"
  [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.var Flapjack.VarKind.local "p"]

def body765_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body765_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_fp_encode64"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "aff", Flapjack.Exp.const 48#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.const 64#64]]

def body765_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body765_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body765_5 : Prog (BitVec 64) :=
.seq body765_3 body765_4

def body765_6 : Prog (BitVec 64) :=
.seq body765_2 body765_5

def body765_7 : Prog (BitVec 64) :=
.seq body765_1 body765_6

def body765_8 : Prog (BitVec 64) :=
.seq body765_0 body765_7

def body765_9 : Prog (BitVec 64) :=
.decCall ("aff") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body765_8

def body765_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body765_9

def body765_11 : Prog (BitVec 64) :=
.seq body765_0 body765_1

def body765_12 : Prog (BitVec 64) :=
.seq body765_11 body765_2

def body765_13 : Prog (BitVec 64) :=
.seq body765_12 body765_3

def body765_14 : Prog (BitVec 64) :=
.seq body765_13 body765_4

def body765_15 : Prog (BitVec 64) :=
.decCall ("aff") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 96#64]) body765_14

def body765_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body765_15

def originalData765 : Decl (BitVec 64) :=
.function { name := "g1_encode", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body765_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData765 : Decl (BitVec 64) :=
.function { name := "g1_encode", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body765_16, returnShape := (Flapjack.Shape.one) }
def original765 := Pancake.PanLang.declToHOL originalData765
def simplified765 := Pancake.PanLang.declToHOL simplifiedData765
end InitECandidate.Proofs.FrontendStages.Declarations
