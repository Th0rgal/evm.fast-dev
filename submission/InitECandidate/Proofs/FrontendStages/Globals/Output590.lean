import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data590
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate574
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody590_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_truncate"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 168#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 264#64])]

def globalBody590_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_truncate"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 176#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 272#64])]

def globalBody590_2 : Prog (BitVec 64) :=
.seq globalBody590_0 globalBody590_1

def globalBody590_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody590_4 : Prog (BitVec 64) :=
.seq globalBody590_2 globalBody590_3

def globalData590 : Decl (BitVec 64) :=
.function { name := "rollback_child_access", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := globalBody590_4, returnShape := (Flapjack.Shape.one) }
def globalOutput590 := Pancake.PanLang.declToHOL globalData590
end InitECandidate.Proofs.FrontendStages.Declarations
