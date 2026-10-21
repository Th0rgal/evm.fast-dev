import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify193
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body209_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def body209_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 20#64],
    Flapjack.Exp.const 48#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def body209_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 68#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64]]

def body209_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 3#64, Flapjack.Exp.const 3#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body209_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body209_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body209_6 : Prog (BitVec 64) :=
.seq body209_4 body209_5

def body209_7 : Prog (BitVec 64) :=
.seq body209_3 body209_6

def body209_8 : Prog (BitVec 64) :=
.seq body209_2 body209_7

def body209_9 : Prog (BitVec 64) :=
.seq body209_1 body209_8

def body209_10 : Prog (BitVec 64) :=
.seq body209_0 body209_9

def body209_11 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.const 32#64]]) body209_10

def body209_12 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body209_11

def body209_13 : Prog (BitVec 64) :=
.seq body209_0 body209_1

def body209_14 : Prog (BitVec 64) :=
.seq body209_13 body209_2

def body209_15 : Prog (BitVec 64) :=
.seq body209_14 body209_3

def body209_16 : Prog (BitVec 64) :=
.seq body209_15 body209_4

def body209_17 : Prog (BitVec 64) :=
.seq body209_16 body209_5

def body209_18 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 3#64, Flapjack.Exp.const 32#64]]) body209_17

def body209_19 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body209_18

def originalData209 : Decl (BitVec 64) :=
.function { name := "htr_wdreq", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body209_12, returnShape := (Flapjack.Shape.one) }
def simplifiedData209 : Decl (BitVec 64) :=
.function { name := "htr_wdreq", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body209_19, returnShape := (Flapjack.Shape.one) }
def original209 := Pancake.PanLang.declToHOL originalData209
def simplified209 := Pancake.PanLang.declToHOL simplifiedData209
end InitECandidate.Proofs.FrontendStages.Declarations
