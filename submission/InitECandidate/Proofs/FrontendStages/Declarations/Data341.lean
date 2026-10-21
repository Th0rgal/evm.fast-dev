import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify325
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body341_0 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "zeros"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "zeros", Flapjack.Exp.const 1#64])

def body341_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body341_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal
  (Flapjack.Exp.loadByte
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.var Flapjack.VarKind.local "p", Flapjack.Exp.var Flapjack.VarKind.local "i"]))
  (Flapjack.Exp.const 0#64)) body341_0 body341_1

def body341_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "i"
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "i", Flapjack.Exp.const 1#64])

def body341_4 : Prog (BitVec 64) :=
.seq body341_2 body341_3

def body341_5 : Prog (BitVec 64) :=
.while (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "i")
  (Flapjack.Exp.var Flapjack.VarKind.local "n")) body341_4

def body341_6 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.var Flapjack.VarKind.local "zeros",
      Flapjack.Exp.panOp Flapjack.PanOp.mul
        [Flapjack.Exp.op Flapjack.BinOp.sub
            [Flapjack.Exp.var Flapjack.VarKind.local "n", Flapjack.Exp.var Flapjack.VarKind.local "zeros"],
          Flapjack.Exp.const 4#64]])

def body341_7 : Prog (BitVec 64) :=
.seq body341_5 body341_6

def body341_8 : Prog (BitVec 64) :=
.dec ("i") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body341_7

def body341_9 : Prog (BitVec 64) :=
.dec ("zeros") (Flapjack.Shape.one) (Flapjack.Exp.const 0#64) body341_8

def originalData341 : Decl (BitVec 64) :=
.function { name := "count_tokens_in_data", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body341_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData341 : Decl (BitVec 64) :=
.function { name := "count_tokens_in_data", inline := false, exported := false, params := [("p", Flapjack.Shape.one), ("n", Flapjack.Shape.one)], body := body341_9, returnShape := (Flapjack.Shape.one) }
def original341 := Pancake.PanLang.declToHOL originalData341
def simplified341 := Pancake.PanLang.declToHOL simplifiedData341
end InitECandidate.Proofs.FrontendStages.Declarations
