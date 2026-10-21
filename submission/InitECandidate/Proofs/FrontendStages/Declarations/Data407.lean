import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify391
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body407_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "np",
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64]),
    Flapjack.Exp.panOp Flapjack.PanOp.mul
      [Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "n"]]

def body407_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "np")

def body407_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.var Flapjack.VarKind.local "cap", Flapjack.Exp.const 2#64])

def body407_3 : Prog (BitVec 64) :=
.seq body407_1 body407_2

def body407_4 : Prog (BitVec 64) :=
.seq body407_0 body407_3

def body407_5 : Prog (BitVec 64) :=
.decCall ("np") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "cap"],
      Flapjack.Exp.const 2#64]]) body407_4

def body407_6 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body407_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body407_5 body407_6

def body407_8 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.const 1#64])

def body407_9 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 0#64]),
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "esz"]])

def body407_10 : Prog (BitVec 64) :=
.seq body407_8 body407_9

def body407_11 : Prog (BitVec 64) :=
.seq body407_7 body407_10

def body407_12 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 16#64])) body407_11

def body407_13 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) body407_12

def body407_14 : Prog (BitVec 64) :=
.seq body407_0 body407_1

def body407_15 : Prog (BitVec 64) :=
.seq body407_14 body407_2

def body407_16 : Prog (BitVec 64) :=
.decCall ("np") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul
    [Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.var Flapjack.VarKind.local "esz", Flapjack.Exp.var Flapjack.VarKind.local "cap"],
      Flapjack.Exp.const 2#64]]) body407_15

def body407_17 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notLower (Flapjack.Exp.var Flapjack.VarKind.local "n")
  (Flapjack.Exp.var Flapjack.VarKind.local "cap")) body407_16 body407_6

def body407_18 : Prog (BitVec 64) :=
.seq body407_17 body407_8

def body407_19 : Prog (BitVec 64) :=
.seq body407_18 body407_9

def body407_20 : Prog (BitVec 64) :=
.dec ("cap") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 16#64])) body407_19

def body407_21 : Prog (BitVec 64) :=
.dec ("n") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "l", Flapjack.Exp.const 8#64])) body407_20

def originalData407 : Decl (BitVec 64) :=
.function { name := "lst_push", inline := false, exported := false, params := [("l", Flapjack.Shape.one), ("esz", Flapjack.Shape.one)], body := body407_13, returnShape := (Flapjack.Shape.one) }
def simplifiedData407 : Decl (BitVec 64) :=
.function { name := "lst_push", inline := false, exported := false, params := [("l", Flapjack.Shape.one), ("esz", Flapjack.Shape.one)], body := body407_21, returnShape := (Flapjack.Shape.one) }
def original407 := Pancake.PanLang.declToHOL originalData407
def simplified407 := Pancake.PanLang.declToHOL simplifiedData407
end InitECandidate.Proofs.FrontendStages.Declarations
