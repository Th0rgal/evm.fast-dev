import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data214
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate198
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody214_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 0#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 8#64]),
    Flapjack.Exp.const 192#64, Flapjack.Exp.var Flapjack.VarKind.local "ch"]

def globalBody214_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 1#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 16#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 24#64]),
    Flapjack.Exp.const 76#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 32#64]]

def globalBody214_2 : Prog (BitVec 64) :=
.seq globalBody214_0 globalBody214_1

def globalBody214_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 2#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 32#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 40#64]),
    Flapjack.Exp.const 116#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 64#64]]

def globalBody214_4 : Prog (BitVec 64) :=
.seq globalBody214_2 globalBody214_3

def globalBody214_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 3#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.const 184#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 96#64]]

def globalBody214_6 : Prog (BitVec 64) :=
.seq globalBody214_4 globalBody214_5

def globalBody214_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_request_list"
  [Flapjack.Exp.const 4#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 64#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rq", Flapjack.Exp.const 72#64]),
    Flapjack.Exp.const 68#64,
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 128#64]]

def globalBody214_8 : Prog (BitVec 64) :=
.seq globalBody214_6 globalBody214_7

def globalBody214_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htr_pcontainer"
  [Flapjack.Exp.var Flapjack.VarKind.local "ch", Flapjack.Exp.const 5#64, Flapjack.Exp.var Flapjack.VarKind.local "out"]

def globalBody214_10 : Prog (BitVec 64) :=
.seq globalBody214_8 globalBody214_9

def globalBody214_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody214_12 : Prog (BitVec 64) :=
.seq globalBody214_10 globalBody214_11

def globalBody214_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody214_14 : Prog (BitVec 64) :=
.seq globalBody214_12 globalBody214_13

def globalBody214_15 : Prog (BitVec 64) :=
.decCall ("ch") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 5#64, Flapjack.Exp.const 32#64]]) globalBody214_14

def globalBody214_16 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody214_15

def globalData214 : Decl (BitVec 64) :=
.function { name := "htr_requests", inline := false, exported := false, params := [("rq", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := globalBody214_16, returnShape := (Flapjack.Shape.one) }
def globalOutput214 := Pancake.PanLang.declToHOL globalData214
end InitECandidate.Proofs.FrontendStages.Declarations
