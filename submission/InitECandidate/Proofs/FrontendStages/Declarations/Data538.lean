import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify522
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body538_0 : Prog (BitVec 64) :=
Flapjack.Prog.call (some (none, none)) "copy_from_buffer"
  [Flapjack.Exp.const 3#64,
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 48#64]),
    Flapjack.Exp.load Flapjack.Shape.one
      (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 56#64])]

def body538_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body538_2 : Prog (BitVec 64) :=
.seq body538_0 body538_1

def originalData538 : Decl (BitVec 64) :=
.function { name := "op_codecopy", inline := false, exported := false, params := [], body := body538_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData538 : Decl (BitVec 64) :=
.function { name := "op_codecopy", inline := false, exported := false, params := [], body := body538_2, returnShape := (Flapjack.Shape.one) }
def original538 := Pancake.PanLang.declToHOL originalData538
def simplified538 := Pancake.PanLang.declToHOL simplifiedData538
end InitECandidate.Proofs.FrontendStages.Declarations
