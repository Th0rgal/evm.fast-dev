import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data230
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate212
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody230_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "r")

def globalBody230_1 : Prog (BitVec 64) :=
.decCall ("r") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) ("taylor_exponential") ([Flapjack.Exp.const 1#64, Flapjack.Exp.var Flapjack.VarKind.local "excess_blob_gas", Flapjack.Exp.const 11684671#64]) globalBody230_0

def globalData230 : Decl (BitVec 64) :=
.function { name := "calculate_blob_gas_price", inline := false, exported := false, params := [("excess_blob_gas", Flapjack.Shape.one)], body := globalBody230_1, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def globalOutput230 := Pancake.PanLang.declToHOL globalData230
end InitECandidate.Proofs.FrontendStages.Declarations
