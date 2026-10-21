import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify227
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body243_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "MptErr" (Flapjack.Exp.var Flapjack.VarKind.local "code")

def body243_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body243_2 : Prog (BitVec 64) :=
.seq body243_0 body243_1

def originalData243 : Decl (BitVec 64) :=
.function { name := "mpt_fail", inline := false, exported := false, params := [("code", Flapjack.Shape.one)], body := body243_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData243 : Decl (BitVec 64) :=
.function { name := "mpt_fail", inline := false, exported := false, params := [("code", Flapjack.Shape.one)], body := body243_2, returnShape := (Flapjack.Shape.one) }
def original243 := Pancake.PanLang.declToHOL originalData243
def simplified243 := Pancake.PanLang.declToHOL simplifiedData243
end InitECandidate.Proofs.FrontendStages.Declarations
