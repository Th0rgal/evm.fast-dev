import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify782
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body798_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "bls_consts_init" []

def body798_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body798_2 : Prog (BitVec 64) :=
.seq body798_0 body798_1

def originalData798 : Decl (BitVec 64) :=
.function { name := "bls_lib_init", inline := false, exported := false, params := [], body := body798_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData798 : Decl (BitVec 64) :=
.function { name := "bls_lib_init", inline := false, exported := false, params := [], body := body798_2, returnShape := (Flapjack.Shape.one) }
def original798 := Pancake.PanLang.declToHOL originalData798
def simplified798 := Pancake.PanLang.declToHOL simplifiedData798
end InitECandidate.Proofs.FrontendStages.Declarations
