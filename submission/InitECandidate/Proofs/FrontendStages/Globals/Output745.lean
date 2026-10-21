import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data745
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate729
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody745_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_set_one" [Flapjack.Exp.var Flapjack.VarKind.local "r"]

def globalBody745_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fp6_set_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 288#64]]

def globalBody745_2 : Prog (BitVec 64) :=
.seq globalBody745_0 globalBody745_1

def globalBody745_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody745_4 : Prog (BitVec 64) :=
.seq globalBody745_2 globalBody745_3

def globalData745 : Decl (BitVec 64) :=
.function { name := "fp12_set_one", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := globalBody745_4, returnShape := (Flapjack.Shape.one) }
def globalOutput745 := Pancake.PanLang.declToHOL globalData745
end InitECandidate.Proofs.FrontendStages.Declarations
