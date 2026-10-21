import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify195
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body211_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 48#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def body211_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 48#64],
    Flapjack.Exp.const 32#64]

def body211_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_u64_at"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 80#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64]]

def body211_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_bytes_vector"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "e", Flapjack.Exp.const 88#64],
    Flapjack.Exp.const 96#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 96#64]]

def body211_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 4#64, Flapjack.Exp.const 4#64,
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body211_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body211_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body211_7 : Prog (BitVec 64) :=
.seq body211_5 body211_6

def body211_8 : Prog (BitVec 64) :=
.seq body211_4 body211_7

def body211_9 : Prog (BitVec 64) :=
.seq body211_3 body211_8

def body211_10 : Prog (BitVec 64) :=
.seq body211_2 body211_9

def body211_11 : Prog (BitVec 64) :=
.seq body211_1 body211_10

def body211_12 : Prog (BitVec 64) :=
.seq body211_0 body211_11

def body211_13 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 4#64, Flapjack.Exp.const 32#64]]) body211_12

def body211_14 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body211_13

def body211_15 : Prog (BitVec 64) :=
.seq body211_0 body211_1

def body211_16 : Prog (BitVec 64) :=
.seq body211_15 body211_2

def body211_17 : Prog (BitVec 64) :=
.seq body211_16 body211_3

def body211_18 : Prog (BitVec 64) :=
.seq body211_17 body211_4

def body211_19 : Prog (BitVec 64) :=
.seq body211_18 body211_5

def body211_20 : Prog (BitVec 64) :=
.seq body211_19 body211_6

def body211_21 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 4#64, Flapjack.Exp.const 32#64]]) body211_20

def body211_22 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body211_21

def originalData211 : Decl (BitVec 64) :=
.function { name := "htr_bdep", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body211_14, returnShape := (Flapjack.Shape.one) }
def simplifiedData211 : Decl (BitVec 64) :=
.function { name := "htr_bdep", inline := false, exported := false, params := [("e", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body211_22, returnShape := (Flapjack.Shape.one) }
def original211 := Pancake.PanLang.declToHOL originalData211
def simplified211 := Pancake.PanLang.declToHOL simplifiedData211
end InitECandidate.Proofs.FrontendStages.Declarations
