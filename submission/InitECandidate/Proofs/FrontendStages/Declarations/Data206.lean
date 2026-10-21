import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify190
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body206_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "merkleize"
  [Flapjack.Exp.var Flapjack.VarKind.local "roots", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "lim", Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body206_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "mix_in_length"
  [Flapjack.Exp.var Flapjack.VarKind.local "out", Flapjack.Exp.var Flapjack.VarKind.local "n",
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body206_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body206_3 : Prog (BitVec 64) :=
.seq body206_1 body206_2

def body206_4 : Prog (BitVec 64) :=
.seq body206_0 body206_3

def body206_5 : Prog (BitVec 64) :=
.seq body206_0 body206_1

def body206_6 : Prog (BitVec 64) :=
.seq body206_5 body206_2

def originalData206 : Decl (BitVec 64) :=
.function { name := "htr_list_roots", inline := false, exported := false, params := [("roots", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("lim", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body206_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData206 : Decl (BitVec 64) :=
.function { name := "htr_list_roots", inline := false, exported := false, params := [("roots", Flapjack.Shape.one), ("n", Flapjack.Shape.one), ("lim", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body206_6, returnShape := (Flapjack.Shape.one) }
def original206 := Pancake.PanLang.declToHOL originalData206
def simplified206 := Pancake.PanLang.declToHOL simplifiedData206
end InitECandidate.Proofs.FrontendStages.Declarations
