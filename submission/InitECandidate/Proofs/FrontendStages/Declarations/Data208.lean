import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify192
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body208_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 48#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def body208_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 48#64],
    Flapjack.Exp.const 32#64]

def body208_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 80#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64]]

def body208_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 88#64],
    Flapjack.Exp.const 96#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 96#64]]

def body208_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 184#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 128#64]]

def body208_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 5#64, Flapjack.Exp.const 5#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body208_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body208_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body208_8 : Prog (BitVec 64) :=
.seq body208_6 body208_7

def body208_9 : Prog (BitVec 64) :=
.seq body208_5 body208_8

def body208_10 : Prog (BitVec 64) :=
.seq body208_4 body208_9

def body208_11 : Prog (BitVec 64) :=
.seq body208_3 body208_10

def body208_12 : Prog (BitVec 64) :=
.seq body208_2 body208_11

def body208_13 : Prog (BitVec 64) :=
.seq body208_1 body208_12

def body208_14 : Prog (BitVec 64) :=
.seq body208_0 body208_13

def body208_15 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 32#64]]) body208_14

def body208_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body208_15

def body208_17 : Prog (BitVec 64) :=
.seq body208_0 body208_1

def body208_18 : Prog (BitVec 64) :=
.seq body208_17 body208_2

def body208_19 : Prog (BitVec 64) :=
.seq body208_18 body208_3

def body208_20 : Prog (BitVec 64) :=
.seq body208_19 body208_4

def body208_21 : Prog (BitVec 64) :=
.seq body208_20 body208_5

def body208_22 : Prog (BitVec 64) :=
.seq body208_21 body208_6

def body208_23 : Prog (BitVec 64) :=
.seq body208_22 body208_7

def body208_24 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 32#64]]) body208_23

def body208_25 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body208_24

def originalData208 : Decl (BitVec 64) :=
.function { name := "htr_deposit", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body208_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData208 : Decl (BitVec 64) :=
.function { name := "htr_deposit", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body208_25, returnShape := (Flapjack.Shape.one) }
def original208 := Pancake.PanLang.declToHOL originalData208
def simplified208 := Pancake.PanLang.declToHOL simplifiedData208
end InitECandidate.Proofs.FrontendStages.Declarations
