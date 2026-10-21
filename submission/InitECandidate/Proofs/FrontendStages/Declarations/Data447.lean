import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify431
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body447_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "from_gl"])

def body447_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "spilled", Flapjack.Exp.var Flapjack.VarKind.local "from_gl"])

def body447_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64]),
      Flapjack.Exp.op Flapjack.BinOp.sub
        [Flapjack.Exp.var Flapjack.VarKind.local "amount", Flapjack.Exp.var Flapjack.VarKind.local "from_gl"]])

def body447_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body447_4 : Prog (BitVec 64) :=
.seq body447_2 body447_3

def body447_5 : Prog (BitVec 64) :=
.seq body447_1 body447_4

def body447_6 : Prog (BitVec 64) :=
.seq body447_0 body447_5

def body447_7 : Prog (BitVec 64) :=
.decCall ("from_gl") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "amount", Flapjack.Exp.var Flapjack.VarKind.local "spilled"]) body447_6

def body447_8 : Prog (BitVec 64) :=
.dec ("spilled") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])) body447_7

def body447_9 : Prog (BitVec 64) :=
.seq body447_0 body447_1

def body447_10 : Prog (BitVec 64) :=
.seq body447_9 body447_2

def body447_11 : Prog (BitVec 64) :=
.seq body447_10 body447_3

def body447_12 : Prog (BitVec 64) :=
.decCall ("from_gl") (Flapjack.Shape.one) ("min") ([Flapjack.Exp.var Flapjack.VarKind.local "amount", Flapjack.Exp.var Flapjack.VarKind.local "spilled"]) body447_11

def body447_13 : Prog (BitVec 64) :=
.dec ("spilled") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])) body447_12

def originalData447 : Decl (BitVec 64) :=
.function { name := "credit_state_gas_refund", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := body447_8, returnShape := (Flapjack.Shape.one) }
def simplifiedData447 : Decl (BitVec 64) :=
.function { name := "credit_state_gas_refund", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := body447_13, returnShape := (Flapjack.Shape.one) }
def original447 := Pancake.PanLang.declToHOL originalData447
def simplified447 := Pancake.PanLang.declToHOL simplifiedData447
end InitECandidate.Proofs.FrontendStages.Declarations
