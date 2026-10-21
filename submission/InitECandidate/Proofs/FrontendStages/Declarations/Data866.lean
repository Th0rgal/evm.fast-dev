import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify850
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body866_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memzero"
  [Flapjack.Exp.var Flapjack.VarKind.local "te", Flapjack.Exp.const 200#64]

def body866_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "te")

def body866_2 : Prog (BitVec 64) :=
.seq body866_0 body866_1

def body866_3 : Prog (BitVec 64) :=
.decCall ("te") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 200#64]) body866_2

def originalData866 : Decl (BitVec 64) :=
.function { name := "te_new", inline := false, exported := false, params := [], body := body866_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData866 : Decl (BitVec 64) :=
.function { name := "te_new", inline := false, exported := false, params := [], body := body866_3, returnShape := (Flapjack.Shape.one) }
def original866 := Pancake.PanLang.declToHOL originalData866
def simplified866 := Pancake.PanLang.declToHOL simplifiedData866
end InitECandidate.Proofs.FrontendStages.Declarations
