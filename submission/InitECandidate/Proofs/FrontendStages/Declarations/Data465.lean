import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify449
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body465_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "n"])

def body465_1 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body465_2 : Prog (BitVec 64) :=
.seq body465_0 body465_1

def originalData465 : Decl (BitVec 64) :=
.function { name := "pc_add", inline := false, exported := false, params := [("n", Flapjack.Shape.one)], body := body465_2, returnShape := (Flapjack.Shape.one) }
def simplifiedData465 : Decl (BitVec 64) :=
.function { name := "pc_add", inline := false, exported := false, params := [("n", Flapjack.Shape.one)], body := body465_2, returnShape := (Flapjack.Shape.one) }
def original465 := Pancake.PanLang.declToHOL originalData465
def simplified465 := Pancake.PanLang.declToHOL simplifiedData465
end InitECandidate.Proofs.FrontendStages.Declarations
