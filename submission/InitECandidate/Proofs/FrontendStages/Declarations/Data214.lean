import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify198
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body214_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 0#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.const 192#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def body214_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 1#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 76#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def body214_2 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 2#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.const 116#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64]]

def body214_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 3#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.const 184#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 96#64]]

def body214_4 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 4#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 64#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 72#64]),
    Flapjack.Exp.const 68#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 128#64]]

def body214_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_pcontainer"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 5#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body214_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def body214_7 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body214_8 : Prog (BitVec 64) :=
.seq body214_6 body214_7

def body214_9 : Prog (BitVec 64) :=
.seq body214_5 body214_8

def body214_10 : Prog (BitVec 64) :=
.seq body214_4 body214_9

def body214_11 : Prog (BitVec 64) :=
.seq body214_3 body214_10

def body214_12 : Prog (BitVec 64) :=
.seq body214_2 body214_11

def body214_13 : Prog (BitVec 64) :=
.seq body214_1 body214_12

def body214_14 : Prog (BitVec 64) :=
.seq body214_0 body214_13

def body214_15 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 32#64]]) body214_14

def body214_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body214_15

def body214_17 : Prog (BitVec 64) :=
.seq body214_0 body214_1

def body214_18 : Prog (BitVec 64) :=
.seq body214_17 body214_2

def body214_19 : Prog (BitVec 64) :=
.seq body214_18 body214_3

def body214_20 : Prog (BitVec 64) :=
.seq body214_19 body214_4

def body214_21 : Prog (BitVec 64) :=
.seq body214_20 body214_5

def body214_22 : Prog (BitVec 64) :=
.seq body214_21 body214_6

def body214_23 : Prog (BitVec 64) :=
.seq body214_22 body214_7

def body214_24 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 32#64]]) body214_23

def body214_25 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) body214_24

def originalData214 : Decl (BitVec 64) :=
.function { name := "htr_requests", inline := false, exported := false, params := [("rq", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body214_16, returnShape := (Flapjack.Shape.one) }
def simplifiedData214 : Decl (BitVec 64) :=
.function { name := "htr_requests", inline := false, exported := false, params := [("rq", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body214_25, returnShape := (Flapjack.Shape.one) }
def original214 := Pancake.PanLang.declToHOL originalData214
def simplified214 := Pancake.PanLang.declToHOL simplifiedData214
end InitECandidate.Proofs.FrontendStages.Declarations
