import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify703
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body719_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero" [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.const 96#64]

def body719_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body719_2 : Prog (BitVec 64) :=
.seq body719_0 body719_1

def originalData719 : Decl (BitVec 64) :=
.function { name := "fp2_set_zero", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body719_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData719 : Decl (BitVec 64) :=
.function { name := "fp2_set_zero", inline := false, exported := false, params := [("r", Flapjack.Shape.one)], body := body719_2, returnShape := (Flapjack.Shape.one) }
def original719 := Pancake.PanLang.declToHOL originalData719
def simplified719 := Pancake.PanLang.declToHOL simplifiedData719
end InitECandidate.Proofs.FrontendStages.Declarations
