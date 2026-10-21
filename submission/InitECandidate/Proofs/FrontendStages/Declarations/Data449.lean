import InitECandidate.Proofs.FrontendComputation
import InitECandidate.Proofs.FrontendStages.Declarations.Simplify433
set_option Elab.async false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
open scoped InitECandidate.Proofs.FrontendComputation
open Flapjack
namespace InitECandidate.Proofs.FrontendStages.Declarations
def body449_0 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64])
  (Flapjack.Exp.op Flapjack.BinOp.add
    [Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 64#64]),
      Flapjack.Exp.load Flapjack.Shape.one
        (Flapjack.Exp.op Flapjack.BinOp.add
          [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])])

def body449_1 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 72#64])
  (Flapjack.Exp.load Flapjack.Shape.one
    (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.local "msg", Flapjack.Exp.const 48#64]))

def body449_2 : Prog (BitVec 64) :=
Flapjack.Prog.store
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 192#64])
  (Flapjack.Exp.const 0#64)

def body449_3 : Prog (BitVec 64) :=
Flapjack.Prog.return (Flapjack.Exp.const 0#64)

def body449_4 : Prog (BitVec 64) :=
.seq body449_2 body449_3

def body449_5 : Prog (BitVec 64) :=
.seq body449_1 body449_4

def body449_6 : Prog (BitVec 64) :=
.seq body449_0 body449_5

def body449_7 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body449_6

def body449_8 : Prog (BitVec 64) :=
.seq body449_0 body449_1

def body449_9 : Prog (BitVec 64) :=
.seq body449_8 body449_2

def body449_10 : Prog (BitVec 64) :=
.seq body449_9 body449_3

def body449_11 : Prog (BitVec 64) :=
.dec ("msg") (Flapjack.Shape.one) (Flapjack.Exp.load Flapjack.Shape.one
  (Flapjack.Exp.op Flapjack.BinOp.add [Flapjack.Exp.var Flapjack.VarKind.global "ev", Flapjack.Exp.const 112#64])) body449_10

def originalData449 : Decl (BitVec 64) :=
.function { name := "refill_frame_state_gas", inline := false, exported := false, params := [], body := body449_7, returnShape := (Flapjack.Shape.one) }
def simplifiedData449 : Decl (BitVec 64) :=
.function { name := "refill_frame_state_gas", inline := false, exported := false, params := [], body := body449_11, returnShape := (Flapjack.Shape.one) }
def original449 := Pancake.PanLang.declToHOL originalData449
def simplified449 := Pancake.PanLang.declToHOL simplifiedData449
end InitECandidate.Proofs.FrontendStages.Declarations
