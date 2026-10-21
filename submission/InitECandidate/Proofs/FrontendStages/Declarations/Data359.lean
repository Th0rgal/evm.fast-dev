import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify343
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body359_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "a")

def body359_1 : Prog (BitVec 64) :=
.decCall ("a") (Flapjack.Shape.one) ("acct_new") ([Flapjack.Exp.const 0#64,
  Flapjack.Exp.rStruct
    [Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64, Flapjack.Exp.const 0#64],
  Flapjack.Exp.var Flapjack.VarKind.global "empty_code_hash"]) body359_0

def originalData359 : Decl (BitVec 64) :=
.function { name := "acct_empty", inline := false, exported := false, params := [], body := body359_1, returnShape := (Flapjack.Shape.one) }
def simplifiedData359 : Decl (BitVec 64) :=
.function { name := "acct_empty", inline := false, exported := false, params := [], body := body359_1, returnShape := (Flapjack.Shape.one) }
def original359 := Pancake.PanLang.declToHOL originalData359
def simplified359 := Pancake.PanLang.declToHOL simplifiedData359
end InitECandidate.Proofs.FrontendStages.Declarations
