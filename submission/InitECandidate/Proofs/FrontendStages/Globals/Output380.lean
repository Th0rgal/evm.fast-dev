import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data380
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate364
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody380_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody380_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody380_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) globalBody380_0 globalBody380_1

def globalBody380_3 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "eq") (Flapjack.Exp.const 0#64)) globalBody380_0 globalBody380_1

def globalBody380_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual (Flapjack.Exp.var Flapjack.VarKind.local "hs") (Flapjack.Exp.const 0#64)) globalBody380_0 globalBody380_1

def globalBody380_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody380_6 : Prog (BitVec 64) :=
.seq globalBody380_4 globalBody380_5

def globalBody380_7 : Prog (BitVec 64) :=
.decCall ("hs") (Flapjack.Shape.one) ("account_has_storage") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody380_6

def globalBody380_8 : Prog (BitVec 64) :=
.seq globalBody380_3 globalBody380_7

def globalBody380_9 : Prog (BitVec 64) :=
.decCall ("eq") (Flapjack.Shape.one) ("memeq") ([Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 48#64]),
  Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 136#64]),
  Flapjack.Exp.const 32#64]) globalBody380_8

def globalBody380_10 : Prog (BitVec 64) :=
.seq globalBody380_2 globalBody380_9

def globalBody380_11 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("get_account") ([Flapjack.Exp.var Flapjack.VarKind.local "addr"]) globalBody380_10

def globalData380 : Decl (BitVec 64) :=
.function { name := "account_deployable", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody380_11, returnShape := (Flapjack.Shape.one) }
def globalOutput380 := Pancake.PanLang.declToHOL globalData380
end InitECandidate.Proofs.FrontendStages.Declarations
