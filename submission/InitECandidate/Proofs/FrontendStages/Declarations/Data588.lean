import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify572
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body588_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 64#64])])

def body588_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 72#64])])

def body588_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 184#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 184#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.local "child", Flapjack.Exp.const 184#64])])

def body588_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body588_4 : Prog (BitVec 64) :=
.seq body588_2 body588_3

def body588_5 : Prog (BitVec 64) :=
.seq body588_1 body588_4

def body588_6 : Prog (BitVec 64) :=
.seq body588_0 body588_5

def body588_7 : Prog (BitVec 64) :=
.seq body588_0 body588_1

def body588_8 : Prog (BitVec 64) :=
.seq body588_7 body588_2

def body588_9 : Prog (BitVec 64) :=
.seq body588_8 body588_3

def originalData588 : Decl (BitVec 64) :=
.function { name := "incorporate_child_on_error", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := body588_6, returnShape := (Flapjack.Shape.one) }
def simplifiedData588 : Decl (BitVec 64) :=
.function { name := "incorporate_child_on_error", inline := false, exported := false, params := [("child", Flapjack.Shape.one)], body := body588_9, returnShape := (Flapjack.Shape.one) }
def original588 := Pancake.PanLang.declToHOL originalData588
def simplified588 := Pancake.PanLang.declToHOL simplifiedData588
end InitECandidate.Proofs.FrontendStages.Declarations
