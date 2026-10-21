import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify339
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body355_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.global "journal_n")

def originalData355 : Decl (BitVec 64) :=
.function { name := "state_snapshot", inline := false, exported := false, params := [], body := body355_0, returnShape := (Flapjack.Shape.one) }
def simplifiedData355 : Decl (BitVec 64) :=
.function { name := "state_snapshot", inline := false, exported := false, params := [], body := body355_0, returnShape := (Flapjack.Shape.one) }
def original355 := Pancake.PanLang.declToHOL originalData355
def simplified355 := Pancake.PanLang.declToHOL simplifiedData355
end InitECandidate.Proofs.FrontendStages.Declarations
