import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify344
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body360_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "memcpy"
  [Flapjack.Exp.var Flapjack.VarKind.local "b", Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.const 56#64]

def body360_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "b")

def body360_2 : Prog (BitVec 64) :=
.seq body360_0 body360_1

def body360_3 : Prog (BitVec 64) :=
.decCall ("b") (Flapjack.Shape.one) ("alloc") ([Flapjack.Exp.const 56#64]) body360_2

def originalData360 : Decl (BitVec 64) :=
.function { name := "acct_copy", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := body360_3, returnShape := (Flapjack.Shape.one) }
def simplifiedData360 : Decl (BitVec 64) :=
.function { name := "acct_copy", inline := false, exported := false, params := [("a", Flapjack.Shape.one)], body := body360_3, returnShape := (Flapjack.Shape.one) }
def original360 := Pancake.PanLang.declToHOL originalData360
def simplified360 := Pancake.PanLang.declToHOL simplifiedData360
end InitECandidate.Proofs.FrontendStages.Declarations
