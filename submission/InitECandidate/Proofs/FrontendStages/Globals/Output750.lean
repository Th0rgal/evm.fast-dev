import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data750
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate734
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody750_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "a"]

def globalBody750_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64]]

def globalBody750_2 : Prog (BitVec 64) :=
.seq globalBody750_0 globalBody750_1

def globalBody750_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul_v"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody750_4 : Prog (BitVec 64) :=
.seq globalBody750_2 globalBody750_3

def globalBody750_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody750_6 : Prog (BitVec 64) :=
.seq globalBody750_4 globalBody750_5

def globalBody750_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_inv"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "d"]

def globalBody750_8 : Prog (BitVec 64) :=
.seq globalBody750_6 globalBody750_7

def globalBody750_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "d"]

def globalBody750_10 : Prog (BitVec 64) :=
.seq globalBody750_8 globalBody750_9

def globalBody750_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64],
    Flapjack.Exp.var Flapjack.VarKind.local "d"]

def globalBody750_12 : Prog (BitVec 64) :=
.seq globalBody750_10 globalBody750_11

def globalBody750_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_neg"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64]]

def globalBody750_14 : Prog (BitVec 64) :=
.seq globalBody750_12 globalBody750_13

def globalBody750_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody750_16 : Prog (BitVec 64) :=
.seq globalBody750_14 globalBody750_15

def globalBody750_17 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody750_18 : Prog (BitVec 64) :=
.seq globalBody750_16 globalBody750_17

def globalBody750_19 : Prog (BitVec 64) :=
.dec ("d") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) globalBody750_18

def globalBody750_20 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) globalBody750_19

def globalBody750_21 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") globalBody750_20

def globalBody750_22 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 288#64, Flapjack.Exp.const 3#64]]) globalBody750_21

def globalBody750_23 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody750_22

def globalData750 : Decl (BitVec 64) :=
.function { name := "fp12_inv", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := globalBody750_23, returnShape := (Flapjack.Shape.one) }
def globalOutput750 := Pancake.PanLang.declToHOL globalData750
end InitECandidate.Proofs.FrontendStages.Declarations
