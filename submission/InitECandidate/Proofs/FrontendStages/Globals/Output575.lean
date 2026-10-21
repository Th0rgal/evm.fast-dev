import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data575
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate555
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody575_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 104#64]

def globalBody575_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "parent")

def globalBody575_2 : Prog (BitVec 64) :=
.seq globalBody575_0 globalBody575_1

def globalBody575_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 8#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]))

def globalBody575_4 : Prog (BitVec 64) :=
.seq globalBody575_2 globalBody575_3

def globalBody575_5 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "kind")

def globalBody575_6 : Prog (BitVec 64) :=
.seq globalBody575_4 globalBody575_5

def globalBody575_7 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "rec", Flapjack.Exp.const 40#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "msg")

def globalBody575_8 : Prog (BitVec 64) :=
.seq globalBody575_6 globalBody575_7

def globalBody575_9 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "child")

def globalBody575_10 : Prog (BitVec 64) :=
.seq globalBody575_8 globalBody575_9

def globalBody575_11 : Prog (BitVec 64) :=
Flapjack.Prog.store (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "rec")

def globalBody575_12 : Prog (BitVec 64) :=
.seq globalBody575_10 globalBody575_11

def globalBody575_13 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "child")

def globalBody575_14 : Prog (BitVec 64) :=
.seq globalBody575_12 globalBody575_13

def globalBody575_15 : Prog (BitVec 64) :=
.decCall ("rec") (Flapjack.Shape.one) ("scratch_alloc") ([Flapjack.Exp.const 104#64]) globalBody575_14

def globalBody575_16 : Prog (BitVec 64) :=
.decCall ("child") (Flapjack.Shape.one) ("frame_new") ([Flapjack.Exp.var Flapjack.VarKind.local "msg"]) globalBody575_15

def globalBody575_17 : Prog (BitVec 64) :=
.dec ("parent") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64])) globalBody575_16

def globalData575 : Decl (BitVec 64) :=
.function { name := "frame_open", inline := false, exported := false, params := [("msg", Flapjack.Shape.one), ("kind", Flapjack.Shape.one)], body := globalBody575_17, returnShape := (Flapjack.Shape.one) }
def globalOutput575 := Pancake.PanLang.declToHOL globalData575
end InitECandidate.Proofs.FrontendStages.Declarations
