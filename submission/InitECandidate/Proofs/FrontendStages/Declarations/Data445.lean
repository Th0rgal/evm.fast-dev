import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify429
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body445_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 4#64)

def body445_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body445_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.lower (Flapjack.Exp.var Flapjack.VarKind.local "gl")
  (Flapjack.Exp.var Flapjack.VarKind.local "amount")) body445_0 body445_1

def body445_3 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.sub
    [Flapjack.Exp.var Flapjack.VarKind.local "gl", Flapjack.Exp.var Flapjack.VarKind.local "amount"])

def body445_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 184#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 184#64]),
      Flapjack.Exp.var Flapjack.VarKind.local "amount"])

def body445_5 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body445_6 : Prog (BitVec 64) :=
.seq body445_4 body445_5

def body445_7 : Prog (BitVec 64) :=
.seq body445_3 body445_6

def body445_8 : Prog (BitVec 64) :=
.seq body445_2 body445_7

def body445_9 : Prog (BitVec 64) :=
.dec ("gl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])) body445_8

def body445_10 : Prog (BitVec 64) :=
.seq body445_2 body445_3

def body445_11 : Prog (BitVec 64) :=
.seq body445_10 body445_4

def body445_12 : Prog (BitVec 64) :=
.seq body445_11 body445_5

def body445_13 : Prog (BitVec 64) :=
.dec ("gl") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])) body445_12

def originalData445 : Decl (BitVec 64) :=
.function { name := "charge_gas", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := body445_9, returnShape := (Flapjack.Shape.one) }
def simplifiedData445 : Decl (BitVec 64) :=
.function { name := "charge_gas", inline := false, exported := false, params := [("amount", Flapjack.Shape.one)], body := body445_13, returnShape := (Flapjack.Shape.one) }
def original445 := Pancake.PanLang.declToHOL originalData445
def simplified445 := Pancake.PanLang.declToHOL simplifiedData445
end InitECandidate.Proofs.FrontendStages.Declarations
