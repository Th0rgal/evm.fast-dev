import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify371
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body387_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "destroy_storage" [Flapjack.Exp.var Flapjack.VarKind.local "addr"]

def body387_1 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "set_account"
  [Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 1#64]

def body387_2 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body387_3 : Prog (BitVec 64) :=
.seq body387_1 body387_2

def body387_4 : Prog (BitVec 64) :=
.seq body387_0 body387_3

def body387_5 : Prog (BitVec 64) :=
.seq body387_0 body387_1

def body387_6 : Prog (BitVec 64) :=
.seq body387_5 body387_2

def originalData387 : Decl (BitVec 64) :=
.function { name := "destroy_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body387_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData387 : Decl (BitVec 64) :=
.function { name := "destroy_account", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body387_6, returnShape := (Flapjack.Shape.one) }
def original387 := Pancake.PanLang.declToHOL originalData387
def simplified387 := Pancake.PanLang.declToHOL simplifiedData387
end InitECandidate.Proofs.FrontendStages.Declarations
