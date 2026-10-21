import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify196
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body212_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def body212_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64],
    Flapjack.Exp.const 48#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def body212_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 2#64, Flapjack.Exp.const 2#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body212_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body212_4 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body212_5 : Prog (BitVec 64) :=
.seq body212_3 body212_4

def body212_6 : Prog (BitVec 64) :=
.seq body212_2 body212_5

def body212_7 : Prog (BitVec 64) :=
.seq body212_1 body212_6

def body212_8 : Prog (BitVec 64) :=
.seq body212_0 body212_7

def body212_9 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 32#64]]) body212_8

def body212_10 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body212_9

def body212_11 : Prog (BitVec 64) :=
.seq body212_0 body212_1

def body212_12 : Prog (BitVec 64) :=
.seq body212_11 body212_2

def body212_13 : Prog (BitVec 64) :=
.seq body212_12 body212_3

def body212_14 : Prog (BitVec 64) :=
.seq body212_13 body212_4

def body212_15 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 2#64, Flapjack.Exp.const 32#64]]) body212_14

def body212_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body212_15

def originalData212 : Decl (BitVec 64) :=
.function { name := "htr_bexit", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body212_10, returnShape := (Flapjack.Shape.one) }
def simplifiedData212 : Decl (BitVec 64) :=
.function { name := "htr_bexit", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body212_16, returnShape := (Flapjack.Shape.one) }
def original212 := Pancake.PanLang.declToHOL originalData212
def simplified212 := Pancake.PanLang.declToHOL simplifiedData212
end InitECandidate.Proofs.FrontendStages.Declarations
