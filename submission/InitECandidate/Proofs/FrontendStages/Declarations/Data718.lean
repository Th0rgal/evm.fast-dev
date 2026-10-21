import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify702
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body718_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "r", Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 96#64]

def body718_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body718_2 : Prog (BitVec 64) :=
.seq body718_0 body718_1

def originalData718 : Decl (BitVec 64) :=
.function { name := "fp2_copy", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body718_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData718 : Decl (BitVec 64) :=
.function { name := "fp2_copy", inline := false, exported := false, params := [("r", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body718_2, returnShape := (Flapjack.Shape.one) }
def original718 := Pancake.PanLang.declToHOL originalData718
def simplified718 := Pancake.PanLang.declToHOL simplifiedData718
end InitECandidate.Proofs.FrontendStages.Declarations
