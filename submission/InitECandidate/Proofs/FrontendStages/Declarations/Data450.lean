import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify434
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body450_0 : Prog (BitVec 64) :=
Flapjack.Prog.raise "EvmErr" (Flapjack.Exp.const 2#64)

def body450_1 : Prog (BitVec 64) :=
Flapjack.Prog.skip

def body450_2 : Prog (BitVec 64) :=
.ite (Flapjack.Exp.cmp Flapjack.Cmp.equal (Flapjack.Exp.var Flapjack.VarKind.local "sp") (Flapjack.Exp.const 0#64)) body450_0 body450_1

def body450_3 : Prog (BitVec 64) :=
Flapjack.Prog.assign Flapjack.VarKind.local "sp"
  (Flapjack.Exp.op Flapjack.BinOp.sub [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 1#64])

def body450_4 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])
  (Flapjack.Exp.var Flapjack.VarKind.local "sp")

def body450_5 : Prog (BitVec 64) :=
Flapjack.Prog.return
  (Flapjack.Exp.load
    (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one])
    (Flapjack.Exp.op Flapjack.BinOp.add
      [Flapjack.Exp.load Flapjack.Shape.one
          (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 8#64]),
        Flapjack.Exp.panOp Flapjack.PanOp.mul
          [Flapjack.Exp.var Flapjack.VarKind.local "sp", Flapjack.Exp.const 32#64]]))

def body450_6 : Prog (BitVec 64) :=
.seq body450_4 body450_5

def body450_7 : Prog (BitVec 64) :=
.seq body450_3 body450_6

def body450_8 : Prog (BitVec 64) :=
.seq body450_2 body450_7

def body450_9 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body450_8

def body450_10 : Prog (BitVec 64) :=
.seq body450_2 body450_3

def body450_11 : Prog (BitVec 64) :=
.seq body450_10 body450_4

def body450_12 : Prog (BitVec 64) :=
.seq body450_11 body450_5

def body450_13 : Prog (BitVec 64) :=
.dec ("sp") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 16#64])) body450_12

def originalData450 : Decl (BitVec 64) :=
.function { name := "stack_pop", inline := false, exported := false, params := [], body := body450_9, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def simplifiedData450 : Decl (BitVec 64) :=
.function { name := "stack_pop", inline := false, exported := false, params := [], body := body450_13, returnShape := (Flapjack.Shape.comb [Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one, Flapjack.Shape.one]) }
def original450 := Pancake.PanLang.declToHOL originalData450
def simplified450 := Pancake.PanLang.declToHOL simplifiedData450
end InitECandidate.Proofs.FrontendStages.Declarations
