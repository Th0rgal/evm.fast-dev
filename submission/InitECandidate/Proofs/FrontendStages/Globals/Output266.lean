import InitECandidate.Proofs.CompactComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Data266
import InitECandidate.Proofs.FrontendStages.Globals.KernelContext
import InitECandidate.Proofs.FrontendStages.Globals.Translate250
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
namespace InitECandidate.Proofs.FrontendStages.Declarations
open Flapjack
def globalBody266_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "mpt_new"
  [Flapjack.Exp.var Flapjack.VarKind.local "root", Flapjack.Exp.var Flapjack.VarKind.local "secured"]

def globalBody266_1 : Prog (BitVec 64) :=
.decCall ("root") (Flapjack.Shape.one) ("decode_witness_to_mpt") ([Flapjack.Exp.var Flapjack.VarKind.local "db", Flapjack.Exp.var Flapjack.VarKind.local "root_hash"]) globalBody266_0

def globalData266 : Decl (BitVec 64) :=
.function { name := "mpt_from_witness", inline := false, exported := false, params := [("db", Flapjack.Shape.one), ("root_hash", Flapjack.Shape.one), ("secured", Flapjack.Shape.one)], body := globalBody266_1, returnShape := (Flapjack.Shape.one) }
def globalOutput266 := Pancake.PanLang.declToHOL globalData266
end InitECandidate.Proofs.FrontendStages.Declarations
