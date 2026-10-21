import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify499
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body515_0 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add
            [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 48#64]),
        Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.const 1#64]))

def body515_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body515_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "pc", Flapjack.Exp.const 1#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 56#64]))) body515_0 body515_1

def body515_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body515_4 : Prog (BitVec 64) :=
.seq body515_2 body515_3

def body515_5 : Prog (BitVec 64) :=
.dec ("pc") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 0#64])) body515_4

def originalData515 : Decl (BitVec 64) :=
.function { name := "code_imm", inline := false, exported := false, params := [], body := body515_5, returnShape := (Flapjack.Shape.one) }
def simplifiedData515 : Decl (BitVec 64) :=
.function { name := "code_imm", inline := false, exported := false, params := [], body := body515_5, returnShape := (Flapjack.Shape.one) }
def original515 := Pancake.PanLang.declToHOL originalData515
def simplified515 := Pancake.PanLang.declToHOL simplifiedData515
end InitECandidate.Proofs.FrontendStages.Declarations
