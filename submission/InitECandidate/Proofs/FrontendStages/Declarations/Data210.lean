import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify194
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body210_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def body210_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64],
    Flapjack.Exp.const 48#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def body210_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 68#64],
    Flapjack.Exp.const 48#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64]]

def body210_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 3#64, Flapjack.Exp.const 3#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body210_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body210_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body210_6 : Prog (BitVec 64) :=
.seq body210_4 body210_5

def body210_7 : Prog (BitVec 64) :=
.seq body210_3 body210_6

def body210_8 : Prog (BitVec 64) :=
.seq body210_2 body210_7

def body210_9 : Prog (BitVec 64) :=
.seq body210_1 body210_8

def body210_10 : Prog (BitVec 64) :=
.seq body210_0 body210_9

def body210_11 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.const 32#64]]) body210_10

def body210_12 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body210_11

def body210_13 : Prog (BitVec 64) :=
.seq body210_0 body210_1

def body210_14 : Prog (BitVec 64) :=
.seq body210_13 body210_2

def body210_15 : Prog (BitVec 64) :=
.seq body210_14 body210_3

def body210_16 : Prog (BitVec 64) :=
.seq body210_15 body210_4

def body210_17 : Prog (BitVec 64) :=
.seq body210_16 body210_5

def body210_18 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.const 32#64]]) body210_17

def body210_19 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body210_18

def originalData210 : Decl (BitVec 64) :=
.function { name := "htr_cons", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body210_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData210 : Decl (BitVec 64) :=
.function { name := "htr_cons", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body210_19, returnShape := (Flapjack.Shape.one) }
def original210 := Pancake.PanLang.declToHOL originalData210
def simplified210 := Pancake.PanLang.declToHOL simplifiedData210
end InitECandidate.Proofs.FrontendStages.Declarations
