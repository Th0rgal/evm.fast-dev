import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify424
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body440_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.shift Flapjack.Shift.lsr (Flapjack.Exp.var Flapjack.VarKind.local "c") (Flapjack.Exp.const 5#64))

def body440_1 : Prog (BitVec 64) :=
.decCall ("c") (Flapjack.Shape.one) ("ceil32") ([Flapjack.Exp.var Flapjack.VarKind.local "n"]) body440_0

def originalData440 : Decl (BitVec 64) :=
.function { name := "words_of", inline := false, exported := false, params := [("n", Flapjack.Shape.one)], body := body440_1, returnShape := (Flapjack.Shape.one) }
def simplifiedData440 : Decl (BitVec 64) :=
.function { name := "words_of", inline := false, exported := false, params := [("n", Flapjack.Shape.one)], body := body440_1, returnShape := (Flapjack.Shape.one) }
def original440 := Pancake.PanLang.declToHOL originalData440
def simplified440 := Pancake.PanLang.declToHOL simplifiedData440
end InitECandidate.Proofs.FrontendStages.Declarations
