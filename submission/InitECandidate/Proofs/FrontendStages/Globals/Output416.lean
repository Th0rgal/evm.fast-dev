import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data416
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate395
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody416_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bal_ensure_account" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def globalBody416_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def globalBody416_2 : Prog (BitVec 64) :=
.seq globalBody416_0 globalBody416_1

def globalData416 : Decl (BitVec 64) :=
.function { name := "add_touched_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := globalBody416_2, returnShape := (Flapjack.Shape.one) }
def globalOutput416 := Pancake.PanLang.declToHOL globalData416
end InitECandidate.Proofs.FrontendStages.Declarations
