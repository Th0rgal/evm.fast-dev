import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify374
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body390_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "htab_set"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ts", Flapjack.Exp.const 56#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "addr", Flapjack.Exp.const 1#64]

def body390_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body390_2 : Prog (BitVec 64) :=
.seq body390_0 body390_1

def originalData390 : Decl (BitVec 64) :=
.function { name := "mark_account_created", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body390_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData390 : Decl (BitVec 64) :=
.function { name := "mark_account_created", inline := false, exported := false, params := [("addr", Flapjack.Shape.one)], body := body390_2, returnShape := (Flapjack.Shape.one) }
def original390 := Pancake.PanLang.declToHOL originalData390
def simplified390 := Pancake.PanLang.declToHOL simplifiedData390
end InitECandidate.Proofs.FrontendStages.Declarations
