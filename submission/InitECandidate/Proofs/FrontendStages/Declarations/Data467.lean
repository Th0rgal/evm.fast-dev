import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify451
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body467_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 8#64)

def body467_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body467_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.notEqual
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64]),
        Flapjack.Exp.const 144#64]))
  (Flapjack.Exp.const 0#64)) body467_0 body467_1

def body467_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body467_4 : Prog (BitVec 64) :=
.seq body467_2 body467_3

def originalData467 : Decl (BitVec 64) :=
.function { name := "require_not_static", inline := false, exported := false, params := [], body := body467_4, returnShape := (Flapjack.Shape.one) }
def simplifiedData467 : Decl (BitVec 64) :=
.function { name := "require_not_static", inline := false, exported := false, params := [], body := body467_4, returnShape := (Flapjack.Shape.one) }
def original467 := Pancake.PanLang.declToHOL originalData467
def simplified467 := Pancake.PanLang.declToHOL simplifiedData467
end InitECandidate.Proofs.FrontendStages.Declarations
