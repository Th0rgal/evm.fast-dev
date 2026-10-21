import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data399
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate383
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody399_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
      Flapjack.Exp.const 56#64])
  (Flapjack.Exp.const 1#64)

def globalBody399_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
      Flapjack.Exp.const 64#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "offset")

def globalBody399_2 : Prog (BitVec 64) :=
.seq globalBody399_0 globalBody399_1

def globalBody399_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def globalBody399_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
        Flapjack.Exp.const 64#64]))
  (Flapjack.Exp.var Flapjack.VarKind.local "offset")) globalBody399_1 globalBody399_3

def globalBody399_5 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.topAddr, Flapjack.Exp.const 176#64]),
        Flapjack.Exp.const 56#64]))
  (Flapjack.Exp.const 0#64)) globalBody399_2 globalBody399_4

def globalBody399_6 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody399_7 : Prog (BitVec 64) :=
.seq globalBody399_5 globalBody399_6

def globalData399 : Decl (BitVec 64) :=
.function { name := "track_ancestor_access", inline := false, exported := false, params := [("offset", Flapjack.Shape.one)], body := globalBody399_7, returnShape := (Flapjack.Shape.one) }
def globalOutput399 := Pancake.PanLang.declToHOL globalData399
end InitECandidate.Proofs.FrontendStages.Declarations
