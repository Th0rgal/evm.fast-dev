import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify189
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body205_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def body205_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 8#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def body205_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 16#64],
    Flapjack.Exp.const 20#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64]]

def body205_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "w", Flapjack.Exp.const 36#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 96#64]]

def body205_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 4#64, Flapjack.Exp.const 4#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body205_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body205_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body205_7 : Prog (BitVec 64) :=
.seq body205_5 body205_6

def body205_8 : Prog (BitVec 64) :=
.seq body205_4 body205_7

def body205_9 : Prog (BitVec 64) :=
.seq body205_3 body205_8

def body205_10 : Prog (BitVec 64) :=
.seq body205_2 body205_9

def body205_11 : Prog (BitVec 64) :=
.seq body205_1 body205_10

def body205_12 : Prog (BitVec 64) :=
.seq body205_0 body205_11

def body205_13 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 4#64, Flapjack.Exp.const 32#64]]) body205_12

def body205_14 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body205_13

def body205_15 : Prog (BitVec 64) :=
.seq body205_0 body205_1

def body205_16 : Prog (BitVec 64) :=
.seq body205_15 body205_2

def body205_17 : Prog (BitVec 64) :=
.seq body205_16 body205_3

def body205_18 : Prog (BitVec 64) :=
.seq body205_17 body205_4

def body205_19 : Prog (BitVec 64) :=
.seq body205_18 body205_5

def body205_20 : Prog (BitVec 64) :=
.seq body205_19 body205_6

def body205_21 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 4#64, Flapjack.Exp.const 32#64]]) body205_20

def body205_22 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body205_21

def originalData205 : Decl (BitVec 64) :=
.function { name := "htr_withdrawal", inline := false, exported := false, params := [("w", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body205_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData205 : Decl (BitVec 64) :=
.function { name := "htr_withdrawal", inline := false, exported := false, params := [("w", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body205_22, returnShape := (Flapjack.Shape.one) }
def original205 := Pancake.PanLang.declToHOL originalData205
def simplified205 := Pancake.PanLang.declToHOL simplifiedData205
end InitECandidate.Proofs.FrontendStages.Declarations
