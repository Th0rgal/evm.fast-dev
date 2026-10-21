import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data747
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate731
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody747_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t0", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.var Flapjack.VarKind.local "b"]

def globalBody747_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64],
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 288#64]]

def globalBody747_2 : Prog (BitVec 64) :=
.seq globalBody747_0 globalBody747_1

def globalBody747_3 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "sa", Flapjack.Exp.var Flapjack.VarKind.local "a",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 288#64]]

def globalBody747_4 : Prog (BitVec 64) :=
.seq globalBody747_2 globalBody747_3

def globalBody747_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "sb", Flapjack.Exp.var Flapjack.VarKind.local "b",
    Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.const 288#64]]

def globalBody747_6 : Prog (BitVec 64) :=
.seq globalBody747_4 globalBody747_5

def globalBody747_7 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "sa",
    Flapjack.Exp.var Flapjack.VarKind.local "sb"]

def globalBody747_8 : Prog (BitVec 64) :=
.seq globalBody747_6 globalBody747_7

def globalBody747_9 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_sub"
  [Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t2",
    Flapjack.Exp.var Flapjack.VarKind.local "t0"]

def globalBody747_10 : Prog (BitVec 64) :=
.seq globalBody747_8 globalBody747_9

def globalBody747_11 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_sub"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64],
    Flapjack.Exp.var Flapjack.VarKind.local "t2", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody747_12 : Prog (BitVec 64) :=
.seq globalBody747_10 globalBody747_11

def globalBody747_13 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_mul_v"
  [Flapjack.Exp.var Flapjack.VarKind.local "t1", Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody747_14 : Prog (BitVec 64) :=
.seq globalBody747_12 globalBody747_13

def globalBody747_15 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_add"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "t0",
    Flapjack.Exp.var Flapjack.VarKind.local "t1"]

def globalBody747_16 : Prog (BitVec 64) :=
.seq globalBody747_14 globalBody747_15

def globalBody747_17 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "heap_release" [Flapjack.Exp.var Flapjack.VarKind.local "mark"]

def globalBody747_18 : Prog (BitVec 64) :=
.seq globalBody747_16 globalBody747_17

def globalBody747_19 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody747_20 : Prog (BitVec 64) :=
.seq globalBody747_18 globalBody747_19

def globalBody747_21 : Prog (BitVec 64) :=
.dec ("sb") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 1152#64]) globalBody747_20

def globalBody747_22 : Prog (BitVec 64) :=
.dec ("sa") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 864#64]) globalBody747_21

def globalBody747_23 : Prog (BitVec 64) :=
.dec ("t2") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 576#64]) globalBody747_22

def globalBody747_24 : Prog (BitVec 64) :=
.dec ("t1") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "t", Flapjack.Exp.const 288#64]) globalBody747_23

def globalBody747_25 : Prog (BitVec 64) :=
.dec ("t0") (Flapjack.Shape.one) (Flapjack.Exp.var Flapjack.VarKind.local "t") globalBody747_24

def globalBody747_26 : Prog (BitVec 64) :=
.decCall ("t") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.panOp Flapjack.PanOp.mul [Flapjack.Exp.const 288#64, Flapjack.Exp.const 5#64]]) globalBody747_25

def globalBody747_27 : Prog (BitVec 64) :=
.decCall ("mark") (Flapjack.Shape.one) ("heap_mark") ([]) globalBody747_26

def globalData747 : Decl (BitVec 64) :=
.function { name := "fp12_mul", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := globalBody747_27, returnShape := (Flapjack.Shape.one) }
def globalOutput747 := Pancake.PanLang.declToHOL globalData747
end InitECandidate.Proofs.FrontendStages.Declarations
