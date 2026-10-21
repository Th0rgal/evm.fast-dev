import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify422
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body438_0 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 18446744073709551615#64)

def body438_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body438_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "s")
  (Flapjack.Exp.var Flapjack.VarKind.local "a")) body438_0 body438_1

def body438_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "s")

def body438_4 : Prog (BitVec 64) :=
.seq body438_2 body438_3

def body438_5 : Prog (BitVec 64) :=
.dec ("s") (Flapjack.Shape.one) (Flapjack.Exp.op Flapjack.BinOp.add
  [Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "b"]) body438_4

def originalData438 : Decl (BitVec 64) :=
.function { name := "add_sat", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body438_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData438 : Decl (BitVec 64) :=
.function { name := "add_sat", inline := false, exported := false, params := [("a", Flapjack.Shape.one), ("b", Flapjack.Shape.one)], body := body438_5, returnShape := (Flapjack.Shape.one) }
def original438 := Pancake.PanLang.declToHOL originalData438
def simplified438 := Pancake.PanLang.declToHOL simplifiedData438
end InitECandidate.Proofs.FrontendStages.Declarations
