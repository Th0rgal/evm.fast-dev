import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data768
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate752
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody768_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "fp2_is_zero"
  [Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 192#64]]

def globalData768 : Decl (BitVec 64) :=
.function { name := "g2_is_inf", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := globalBody768_0, returnShape := (Flapjack.Shape.one) }
def globalOutput768 := Pancake.PanLang.declToHOL globalData768
end InitECandidate.Proofs.FrontendStages.Declarations
