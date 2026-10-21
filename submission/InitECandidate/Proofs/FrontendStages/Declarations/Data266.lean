import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify250
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body266_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "mpt_new"
  [Flapjack.Exp.var Flapjack.VarKind.local "root", Flapjack.Exp.var Flapjack.VarKind.local "secured"]

def body266_1 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("decode_witness_to_mpt") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.var Flapjack.VarKind.local "root_hash"]) body266_0

def originalData266 : Decl (BitVec 64) :=
.function { name := "mpt_from_witness", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("root_hash", Flapjack.Shape.one), ("secured", Flapjack.Shape.one)], body := body266_1, returnShape := (Flapjack.Shape.one) }
def simplifiedData266 : Decl (BitVec 64) :=
.function { name := "mpt_from_witness", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("root_hash", Flapjack.Shape.one), ("secured", Flapjack.Shape.one)], body := body266_1, returnShape := (Flapjack.Shape.one) }
def original266 := Pancake.PanLang.declToHOL originalData266
def simplified266 := Pancake.PanLang.declToHOL simplifiedData266
end InitECandidate.Proofs.FrontendStages.Declarations
