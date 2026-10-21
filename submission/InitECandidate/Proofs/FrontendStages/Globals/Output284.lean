import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data284
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate268
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody284_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 1#64)

def globalBody284_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody284_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "child") (Flapjack.Exp.const 0#64)) globalBody284_0 globalBody284_1

def globalBody284_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 33#64)

def globalBody284_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 0#64]))
  (Flapjack.Exp.const 0#64)) globalBody284_3 globalBody284_1

def globalBody284_5 : Prog (BitVec 64) :=
.seq globalBody284_2 globalBody284_4

def globalBody284_6 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mpt_fail" [Flapjack.Exp.const 13#64]

def globalBody284_7 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 8#64]))
  (Flapjack.Exp.const 0#64)) globalBody284_6 globalBody284_1

def globalBody284_8 : Prog (BitVec 64) :=
.seq globalBody284_5 globalBody284_7

def globalBody284_9 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "rl")

def globalBody284_10 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "rl") (Flapjack.Exp.const 32#64)) globalBody284_9 globalBody284_1

def globalBody284_11 : Prog (BitVec 64) :=
.seq globalBody284_10 globalBody284_3

def globalBody284_12 : Prog (BitVec 64) :=
.dec ("rl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 16#64])) globalBody284_11

def globalBody284_13 : Prog (BitVec 64) :=
.seq globalBody284_8 globalBody284_12

def globalData284 : Decl (BitVec 64) :=
.function { name := "node_ref_len", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := globalBody284_13, returnShape := (Flapjack.Shape.one) }
def globalOutput284 := Pancake.PanLang.declToHOL globalData284
end InitECandidate.Proofs.FrontendStages.Declarations
