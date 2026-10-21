import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify412
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body428_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "sort_elems"
  [Flapjack.Exp.rField 0 (Flapjack.Exp.var Flapjack.VarKind.local "k"),
    Flapjack.Exp.rField 1 (Flapjack.Exp.var Flapjack.VarKind.local "k"), Flapjack.Exp.const 32#64,
    Flapjack.Exp.const 2#64, Flapjack.Exp.var Flapjack.VarKind.local "tmp"]

def body428_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.var Flapjack.VarKind.local "k")

def body428_2 : Prog (BitVec 64) :=
.seq body428_0 body428_1

def body428_3 : Prog (BitVec 64) :=
.decCall ("k") (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) ("htab_keys") ([Flapjack.Exp.var Flapjack.VarKind.local "t"]) body428_2

def originalData428 : Decl (BitVec 64) :=
.function { name := "sorted_keys32", inline := false, exported := false, params := [("t", Flapjack.Shape.one), ("tmp", Flapjack.Shape.one)], body := body428_3, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData428 : Decl (BitVec 64) :=
.function { name := "sorted_keys32", inline := false, exported := false, params := [("t", Flapjack.Shape.one), ("tmp", Flapjack.Shape.one)], body := body428_3, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one]) }
def original428 := Pancake.PanLang.declToHOL originalData428
def simplified428 := Pancake.PanLang.declToHOL simplifiedData428
end InitECandidate.Proofs.FrontendStages.Declarations
