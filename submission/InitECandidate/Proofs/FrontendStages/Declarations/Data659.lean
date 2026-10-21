import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify643
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body659_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fq12_sqr"
  [Flapjack.Exp.var Flapjack.VarKind.local "d", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body659_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body659_2 : Prog (BitVec 64) :=
.seq body659_0 body659_1

def body659_3 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body659_4 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "fld") (Flapjack.Exp.const 12#64)) body659_2 body659_3

def body659_5 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "fe_mul"
  [Flapjack.Exp.var Flapjack.VarKind.local "fld", Flapjack.Exp.var Flapjack.VarKind.local "d",
    Flapjack.Exp.var Flapjack.VarKind.local "a", Flapjack.Exp.var Flapjack.VarKind.local "a"]

def body659_6 : Prog (BitVec 64) :=
.seq body659_5 body659_1

def body659_7 : Prog (BitVec 64) :=
.seq body659_4 body659_6

def body659_8 : Prog (BitVec 64) :=
.seq body659_4 body659_5

def body659_9 : Prog (BitVec 64) :=
.seq body659_8 body659_1

def originalData659 : Decl (BitVec 64) :=
.function { name := "fe_sqr", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body659_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData659 : Decl (BitVec 64) :=
.function { name := "fe_sqr", inline := false, exported := false, params := [("fld", Flapjack.Shape.one), ("d", Flapjack.Shape.one), ("a", Flapjack.Shape.one)], body := body659_9, returnShape := (Flapjack.Shape.one) }
def original659 := Pancake.PanLang.declToHOL originalData659
def simplified659 := Pancake.PanLang.declToHOL simplifiedData659
end InitECandidate.Proofs.FrontendStages.Declarations
