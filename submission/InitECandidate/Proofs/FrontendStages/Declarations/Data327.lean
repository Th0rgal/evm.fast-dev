import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify311
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body327_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "keccak256"
  [Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 384#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "tx", Flapjack.Exp.const 392#64]),
    Flapjack.Exp.var Flapjack.VarKind.local "out"]

def body327_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body327_2 : Prog (BitVec 64) :=
.seq body327_0 body327_1

def originalData327 : Decl (BitVec 64) :=
.function { name := "get_transaction_hash", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body327_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData327 : Decl (BitVec 64) :=
.function { name := "get_transaction_hash", inline := false, exported := false, params := [("tx", Flapjack.Shape.one), ("out", Flapjack.Shape.one)], body := body327_2, returnShape := (Flapjack.Shape.one) }
def original327 := Pancake.PanLang.declToHOL originalData327
def simplified327 := Pancake.PanLang.declToHOL simplifiedData327
end InitECandidate.Proofs.FrontendStages.Declarations
