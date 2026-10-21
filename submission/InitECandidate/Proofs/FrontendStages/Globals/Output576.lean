import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data576
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate556
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody576_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "refill_frame_state_gas" []

def globalBody576_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "frame_halt" [Flapjack.Exp.var Flapjack.VarKind.local "err"]

def globalBody576_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 120#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 264#64]))

def globalBody576_3 : Prog (BitVec 64) :=
.seq globalBody576_1 globalBody576_2

def globalBody576_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 128#64])
  (Flapjack.Exp.const 0#64)

def globalBody576_5 : Prog (BitVec 64) :=
.seq globalBody576_3 globalBody576_4

def globalBody576_6 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 256#64]),
      Flapjack.Exp.const 160#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "err")

def globalBody576_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "err") (Flapjack.Exp.const 1#64)) globalBody576_5 globalBody576_6

def globalBody576_8 : Prog (BitVec 64) :=
.seq globalBody576_0 globalBody576_7

def globalBody576_9 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 288#64]),
      Flapjack.Exp.const 32#64])
  (Flapjack.Exp.const 1#64)

def globalBody576_10 : Prog (BitVec 64) :=
.seq globalBody576_8 globalBody576_9

def globalBody576_11 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody576_12 : Prog (BitVec 64) :=
.seq globalBody576_10 globalBody576_11

def globalData576 : Decl (BitVec 64) :=
.function { name := "frame_exception", inline := false, exported := false, params := [("err", Flapjack.Shape.one)], body := globalBody576_12, returnShape := (Flapjack.Shape.one) }
def globalOutput576 := Pancake.PanLang.declToHOL globalData576
end InitECandidate.Proofs.FrontendStages.Declarations
