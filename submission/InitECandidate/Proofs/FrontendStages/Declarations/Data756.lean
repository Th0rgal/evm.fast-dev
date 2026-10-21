import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify740
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body756_0 : Prog (BitVec 64) :=
Flapjack.Prog.call none "bls_fp_is_zero" [Flapjack.Exp.var Flapjack.VarKind.local "z"]

def body756_1 : Prog (BitVec 64) :=
.dec ("z") (Flapjack.Shape.comb
  [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
    Flapjack.Shape.one]) (Flapjack.Exp.load
  (Flapjack.Shape.comb
    [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one,
      Flapjack.Shape.one])
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.const 96#64])) body756_0

def originalData756 : Decl (BitVec 64) :=
.function { name := "g1_is_inf", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := body756_1, returnShape := (Flapjack.Shape.one) }
def simplifiedData756 : Decl (BitVec 64) :=
.function { name := "g1_is_inf", inline := false, exported := false, params := [("p", Flapjack.Shape.one)], body := body756_1, returnShape := (Flapjack.Shape.one) }
def original756 := Pancake.PanLang.declToHOL originalData756
def simplified756 := Pancake.PanLang.declToHOL simplifiedData756
end InitECandidate.Proofs.FrontendStages.Declarations
